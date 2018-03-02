struct DomTreeNode
    level::Int
    children::Vector{Int}
end
DomTreeNode() = DomTreeNode(1, Vector{Int}())

struct DomTree
    idoms::Vector{Int}
    nodes::Vector{DomTreeNode}
end

"""
    Checks if bb1 dominates bb2
"""
function dominates(domtree, bb1, bb2)
    bb1 == bb2 && return true
    target_level = domtree.nodes[bb1].level
    source_level = domtree.nodes[bb2].level
    source_level < target_level && return false
    for _ in (source_level-1):-1:target_level
        bb2 = domtree.idoms[bb2]
    end
    return bb1 == bb2
end

function update_level!(domtree, node, level)
    domtree[node] = DomTreeNode(level, domtree[node].children)
    foreach(domtree[node].children) do child
        update_level!(domtree, child, level+1)
    end
end

struct DominatedBlocks
    domtree::DomTree
    worklist::Vector{Int}
end

function dominated(domtree::DomTree, root::Int)
    doms = DominatedBlocks(domtree, Vector{Int}())
    push!(doms.worklist, root)
    doms
end

function start(doms::DominatedBlocks)
    nothing
end

function next(doms::DominatedBlocks, state::Nothing)
    bb = pop!(doms.worklist)
    for dominated in doms.domtree.nodes[bb].children
        push!(doms.worklist, dominated)
    end
    (bb, nothing)
end

function done(doms::DominatedBlocks, state::Nothing)
    isempty(doms.worklist)
end

# Construct Dom Tree
# Simple algorithm - TODO: Switch to the fast version (e.g. https://tanujkhattar.wordpress.com/2016/01/11/dominator-tree-of-a-directed-graph/)
function construct_domtree(cfg)
    dominators = IdSet{Int}[n == 1 ? IdSet{Int}(n) : IdSet{Int}(1:length(cfg.blocks)) for n = 1:length(cfg.blocks)]
    changed = true
    while changed
        changed = false
        for n = 2:length(cfg.blocks)
            isempty(cfg.blocks[n].preds) && continue
            firstp, rest = Iterators.peel(cfg.blocks[n].preds)
            new_doms = copy(dominators[firstp])
            for p in rest
                intersect!(new_doms, dominators[p])
            end
            push!(new_doms, n)
            changed |= (new_doms != dominators[n])
            dominators[n] = new_doms
        end
    end
    # Compute idoms
    idoms = fill(0, length(cfg.blocks))
    for i = 2:length(cfg.blocks)
        for dom in dominators[i]
            i == dom && continue
            any(p->p !== i && p !== dom && dom in dominators[p], dominators[i]) && continue
            idoms[i] = dom
        end
    end
    # Compute children
    domtree = DomTreeNode[DomTreeNode() for _ = 1:length(cfg.blocks)]
    for (idx, idom) in Iterators.enumerate(idoms)
        (idx == 1 || idom == 0) && continue
        push!(domtree[idom].children, idx)
    end
    # Recursively set level
    update_level!(domtree, 1, 1)
    DomTree(idoms, domtree)
end

function rename_phinode_edges(node, bb_rename)
    new_values = Any[]
    new_edges = Any[]
    for (idx, edge) in pairs(node.edges)
        haskey(bb_rename, edge) || continue
        push!(new_edges, bb_rename[edge])
        if isassigned(node.values, idx)
            push!(new_values, node.values[idx])
        else
            resize!(new_values, length(new_values)+1)
        end
    end
    if length(new_edges) == 1
        return isassigned(new_values, 1) ? new_values[1] : PhiNode(Any[], Any[])
    else
        return PhiNode(new_edges, new_values)
    end
end

function domsort_ssa!(ir, domtree)
    # First compute the new order of basic blocks
    result_order = Int[]
    stack = Int[]
    node = 1
    ncritbreaks = 0
    nnewfallthroughs = 0
    while node !== -1
        push!(result_order, node)
        cs = domtree.nodes[node].children
        terminator = ir.stmts[ir.cfg.blocks[node].stmts.last]
        iscondbr = isa(terminator, GotoIfNot)
        old_node = node
        if length(cs) >= 1
            # Adding the nodes in reverse sorted order attempts to retain
            # the original source order of the nodes as much as possible.
            # This is not required for correctness, but is easier on the humans
            if (old_node + 1) in cs
                # Schedule the fall through node first,
                # so we can retain the fall through
                append!(stack, reverse(sort(filter(x->x != old_node + 1, cs))))
                node = node + 1
            else
                append!(stack, reverse(sort(cs)))
                node = pop!(stack)
            end
        else
            if isempty(stack)
                node = -1
            else
                node = pop!(stack)
            end
        end
        if node != old_node + 1 && !isa(terminator, Union{GotoNode, ReturnNode})
            if isa(terminator, GotoIfNot)
                # Need to break the critical edge
                ncritbreaks += 1
                push!(result_order, 0)
            else
                nnewfallthroughs += 1
            end
        end
    end
    bb_rename = IdDict{Int,Int}(i=>x for (x, i) in pairs(result_order) if i !== 0)
    new_bbs = Vector{BasicBlock}(uninitialized, length(result_order))
    nstmts = sum(length(ir.cfg.blocks[i].stmts) for i in result_order if i !== 0)
    result_stmts = Vector{Any}(uninitialized, nstmts+ncritbreaks+nnewfallthroughs)
    result_types = Any[Any for i = 1:length(result_stmts)]
    result_ltable = Int[0 for i = 1:length(result_stmts)]
    inst_rename = Vector{Any}(uninitialized, length(ir.stmts))
    for i = 1:length(ir.new_nodes)
        push!(inst_rename, SSAValue(nstmts + i + ncritbreaks + nnewfallthroughs))
    end
    bb_start_off = 0
    for (new_bb, bb) in pairs(result_order)
        if bb == 0
            bb_start_off += 1
            continue
        end
        old_inst_range = ir.cfg.blocks[bb].stmts
        inst_range = (1:length(old_inst_range)) .+ bb_start_off
        inst_rename[old_inst_range] = Any[SSAValue(x) for x in inst_range]
        for (nidx, idx) in zip(inst_range, old_inst_range)
            stmt = ir.stmts[idx]
            if isa(stmt, PhiNode)
                result_stmts[nidx] = rename_phinode_edges(stmt, bb_rename)
            else
                result_stmts[nidx] = stmt
            end
            result_types[nidx] = ir.types[idx]
            result_ltable[nidx] = ir.lines[idx]
        end
        # Now fix up the terminator
        terminator = result_stmts[inst_range[end]]
        if isa(terminator, GotoNode)
            # Convert to implicit fall through
            if bb_rename[terminator.label] == new_bb + 1
                result_stmts[inst_range[end]] = nothing
            else
                result_stmts[inst_range[end]] = GotoNode(bb_rename[terminator.label])
            end
        elseif isa(terminator, GotoIfNot)
            # Check if we need to break the critical edge
            if bb_rename[bb + 1] != new_bb + 1
                # Add an explicit goto node in the next basic block (we accounted for this above)
                result_stmts[inst_range[end]+1] = GotoNode(bb_rename[bb+1])
            end
            result_stmts[inst_range[end]] = GotoIfNot(terminator.cond, bb_rename[terminator.dest])
        elseif !isa(terminator, ReturnNode)
            if bb_rename[bb + 1] != new_bb + 1
                # Add an explicit goto node
                result_stmts[inst_range[end]+1] = GotoNode(bb_rename[bb+1])
                inst_range = first(inst_range):(last(inst_range)+1)
            end
        end
        bb_start_off += length(inst_range)
        new_preds = Int[bb_rename[i] for i in ir.cfg.blocks[bb].preds if haskey(bb_rename, i)]
        new_succs = Int[bb_rename[i] for i in ir.cfg.blocks[bb].succs if haskey(bb_rename, i)]
        new_bbs[new_bb] = BasicBlock(inst_range, new_preds, new_succs)
    end
    result_stmts = Any[renumber_ssa!(result_stmts[i], inst_rename, true) for i in 1:length(result_stmts)]
    cfg = CFG(new_bbs, Int[first(bb.stmts) for bb in new_bbs[2:end]])
    new_new_nodes = NewNode[(inst_rename[pos].id, typ,
        renumber_ssa!(isa(node, PhiNode) ?
        rename_phinode_edges(node, bb_rename) : node,
        inst_rename, true), lno) for (pos, typ, node, lno) in ir.new_nodes]
    new_ir = IRCode(ir, result_stmts, result_types, result_ltable, cfg, new_new_nodes)
    new_ir
end
