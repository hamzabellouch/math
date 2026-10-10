import OAI.Combinatorics.ContingencyTables.Machines.FiniteGraphCutProgram

namespace OAI

/-! # Exact edge-deletion and cut-metadata computation -/

namespace ContingencyTables.FiniteGraphCutProgram

open SimpleGraph FiniteGraphRootProgram

lemma keep_eq_true_iff (u v i a : ℕ) :
    keep (((u,v),i),a)=true ↔ ¬(i=u ∧ a=v) ∧ ¬(i=v ∧ a=u) := by
  unfold keep
  split_ifs <;> simp_all

variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

lemma deleteRow_graph (u v i : Fin n) :
    deleteRow ((graphCode G,(u.val,v.val)),i.val)=
      adjacencyRow (G.deleteEdges {s(u,v)}) i := by
  unfold deleteRow
  rw [graphCode_getD]
  unfold adjacencyRow
  rw [List.filter_map,List.filter_filter]
  congr 1
  apply List.filter_congr
  intro a _
  apply Bool.eq_iff_iff.mpr
  simp only [Function.comp_apply,Bool.and_eq_true,decide_eq_true_eq,keep_eq_true_iff,
    SimpleGraph.deleteEdges_adj,Set.mem_singleton_iff,Sym2.eq_iff,Fin.ext_iff]
  tauto

theorem deleteGraph_graph (u v : Fin n) :
    deleteGraph (graphCode G,(u.val,v.val))=graphCode (G.deleteEdges {s(u,v)}) := by
  apply List.ext_getElem
  · simp only [deleteGraph,List.length_map,indices,List.length_range,graphCode_length]
  · intro i hi _
    have hi' : i<n := by
      simpa only [deleteGraph,List.length_map,indices,List.length_range,graphCode_length] using hi
    simp only [deleteGraph,indices,List.getElem_map,List.getElem_range]
    rw [deleteRow_graph G u v ⟨i,hi'⟩]
    simp only [graphCode,List.getElem_ofFn]

lemma reachableCode_graph (u v : Fin n) :
    reachableCode ((graphCode G,u.val),v.val)=decide (G.Reachable u v) := by
  apply Bool.eq_iff_iff.mpr
  simp only [reachableCode,decide_eq_true_eq,reached_mem_iff]

theorem awayCode_graph (u v root : Fin n) :
    awayCode ((graphCode G,(u.val,v.val)),root.val)=
      (RootedCut.away G u v root).val := by
  unfold awayCode
  rw [deleteGraph_graph,reachableCode_graph]
  simp only [RootedCut.away,decide_eq_true_eq]
  split_ifs <;> rfl

/-- The executed Boolean metadata is the selected root-away cut in the
actual graph, rather than an arbitrary precomputed cut oracle. -/
theorem cutCode_graph (u v root a : Fin n) :
    cutCode (((graphCode G,(u.val,v.val)),root.val),a.val)=
      RootedCut.cut G u v root a := by
  unfold cutCode
  rw [deleteGraph_graph,awayCode_graph,reachableCode_graph]
  apply Bool.eq_iff_iff.mpr
  simp only [RootedCut.cut,MaximumForest.side,decide_eq_true_eq]

theorem canonicalCutCode_graph (u v a : Fin n) :
    canonicalCutCode ((graphCode G,(u.val,v.val)),a.val)=
      RootedCut.cut G u v (FiniteGraphRoots.root G u) a := by
  unfold canonicalCutCode
  rw [rootCode_eq,cutCode_graph]

end ContingencyTables.FiniteGraphCutProgram

end OAI
