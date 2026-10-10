import OAI.Combinatorics.ContingencyTables.Rooted.ComputedLargeForest

namespace OAI

/-! # The computed forest retains its literal adjacency-list code -/

namespace ContingencyTables.ComputedLargeForest
open SimpleGraph MaximumForest ForestCapacity ForestGreedySemantics
open FiniteGraphRootProgram LargeEdgeCatalogProgram
open scoped Classical

variable {m n : ℕ}

private lemma code_congr {N : ℕ} (G H : SimpleGraph (Fin N))
    [DecidableRel G.Adj] [DecidableRel H.Adj] (h : G=H) : graphCode G=graphCode H := by
  subst H
  apply congrArg (@graphCode N G)
  exact Subsingleton.elim _ _

lemma computed_code (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (W : ℕ) (hW : 1 ≤ W) :
    graphCode ((computed r c b W).comap finSumFinEquiv.symm)=
      ForestGreedyProgram.forest (NetworkVertexCode.data r c b,W) := by
  obtain ⟨F,hF,_⟩ := iterate_optimal (graph b W) ⊥ (capacities b)
    (catalog (NetworkVertexCode.data r c b,W)) (catalog_correct r c b W)
    (capacity_positive b W hW) (MaximumForestExchange.bottom_extendible _ _)
    ((m+n)*(m+n)) (by
      have hb := unordered_pair_budget (n:=m+n)
      omega)
  have hzero (d : DecidableRel (⊥ : SimpleGraph (Fin (m+n))).Adj) :
      @graphCode (m+n) ⊥ d=ForestGreedyProgram.emptyGraph (NetworkVertexCode.data r c b,W) := by
    symm
    simp only [ForestGreedyProgram.emptyGraph,vertexCount_code,DirectedBFSCode.range_eq_map,
      ←List.ofFn_eq_map,List.map_ofFn,graphCode]
    apply congrArg List.ofFn
    funext v
    simp [adjacencyRow]
  have hout : ForestGreedyProgram.forest (NetworkVertexCode.data r c b,W)=graphCode F := by
    unfold ForestGreedyProgram.forest ForestGreedyProgram.prepare
    rw [←hzero (fun a b => Classical.propDecidable _),execute_iterate,graphCode_length]
    exact congrArg Prod.fst hF
  have hc : (computed r c b W).comap finSumFinEquiv.symm=
      decoded (ForestGreedyProgram.forest (NetworkVertexCode.data r c b,W)) := by
    ext u v
    change (decoded (ForestGreedyProgram.forest (NetworkVertexCode.data r c b,W))).Adj
      (vertexEquiv (finSumFinEquiv.symm u)) (vertexEquiv (finSumFinEquiv.symm v)) ↔ _
    simp only [vertexEquiv,Equiv.apply_symm_apply]
  have he : (computed r c b W).comap finSumFinEquiv.symm=F := by
    simpa only [hout,decoded_graphCode] using hc
  exact (code_congr _ _ he).trans hout.symm

end ContingencyTables.ComputedLargeForest

end OAI
