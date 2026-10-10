import OAI.Probability.GammaPassage.LocalTrailPassage
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

namespace OAI

namespace GammaFPP.FiniteLocal
open PlanarFPP Finset

noncomputable def localEdges (p q : Vertex) (R : ℕ) : Finset Edge := by
  classical
  exact (candidates p q R).biUnion (fun ds => ((trace p ds).map traversalEdge).toFinset)

lemma candidate_edges_subset (p q : Vertex) (R : ℕ) (ds : List Step)
    (hds : ds ∈ candidates p q R) :
    ((trace p ds).map traversalEdge).toFinset ⊆ localEdges p q R := by
  classical
  intro e he
  exact Finset.mem_biUnion.mpr ⟨ds, hds, he⟩

abbrev Coordinates (p q : Vertex) (R : ℕ) := (e : ↥(localEdges p q R)) → ℝ

noncomputable def extend (p q : Vertex) (R : ℕ) (v : Coordinates p q R) : Edge → ℝ := by
  classical
  exact fun e => if he : e ∈ localEdges p q R then v ⟨e, he⟩ else 0

@[simp] lemma extend_apply (p q : Vertex) (R : ℕ) (v : Coordinates p q R)
    (e : ↥(localEdges p q R)) : extend p q R v e = v e := by
  classical
  simp [extend, e.property]

lemma extend_nonneg (p q : Vertex) (R : ℕ) (v : Coordinates p q R)
    (hv : ∀ e, 0 ≤ v e) : ∀ e, 0 ≤ extend p q R v e := by
  intro e
  unfold extend
  split_ifs with he
  · exact hv ⟨e, he⟩
  · exact le_rfl

lemma extend_update (p q : Vertex) (R : ℕ) (v : Coordinates p q R)
    (e : ↥(localEdges p q R)) (u : ℝ) :
    extend p q R (Function.update v e u) = Function.update (extend p q R v) e.val u := by
  classical
  funext f
  by_cases hf : f = e.val
  · subst f
    simp [extend, e.property]
  · by_cases hm : f ∈ localEdges p q R
    · have hne : (⟨f, hm⟩ : ↥(localEdges p q R)) ≠ e := by
        intro h
        exact hf (congrArg Subtype.val h)
      simp [extend, hm, Function.update_of_ne hf, Function.update_of_ne hne]
    · simp [extend, hm, Function.update_of_ne hf]

noncomputable def finitePassageTime (p q : Vertex) (R : ℕ)
    (v : Coordinates p q R) : ℝ := passageTime (extend p q R v) p q R

/-- Changing one edge weight changes a trail cost by that weight difference
when the edge belongs to the trail, and by zero otherwise. -/
lemma trailCost_one_edge_change (w w' : Edge → ℝ) (e : Edge)
    (h : ∀ f, f ≠ e → w' f = w f) (p : Vertex) (ds : List Step)
    (hn : ((trace p ds).map traversalEdge).Nodup) :
    pathCost w' p ds - pathCost w p ds =
      if e ∈ (trace p ds).map traversalEdge then w' e - w e else 0 := by
  classical
  rw [pathCost_eq_distinct_edgeSum w' p ds hn, pathCost_eq_distinct_edgeSum w p ds hn,
    ← Finset.sum_sub_distrib]
  by_cases he : e ∈ (trace p ds).map traversalEdge
  · rw [ite_eq_left he]
    apply Finset.sum_eq_single_of_mem e (List.mem_toFinset.mpr he)
    intro f _ hfe
    rw [h f hfe, sub_self]
  · rw [ite_eq_right he]
    apply Finset.sum_eq_zero
    intro f hf
    have hfe : f ≠ e := by
      intro hfe
      exact he (hfe ▸ List.mem_toFinset.mp hf)
    rw [h f hfe, sub_self]

/-- Upward change in the exact finite candidate infimum. -/
noncomputable def upward (w : Edge → ℝ) (p q : Vertex) (R : ℕ)
    (e : Edge) (u : ℝ) : ℝ := by
  classical
  exact max (passageTime (Function.update w e u) p q R - passageTime w p q R) 0

lemma upward_nonneg (w : Edge → ℝ) (p q : Vertex) (R : ℕ) (e : Edge) (u : ℝ) :
    0 ≤ upward w p q R e u := le_max_right _ _

/-- One minimizing trail in the initial environment controls every upward
coordinate-resampling increment. -/
lemma upward_le (w : Edge → ℝ) (hw : ∀ e, 0 ≤ w e)
    (p q : Vertex) (R : ℕ) (ds : List Step) (hds : ds ∈ candidates p q R)
    (hm : pathCost w p ds = passageTime w p q R) (e : Edge) (u : ℝ) (hu : 0 ≤ u) :
    upward w p q R e u ≤ if e ∈ (trace p ds).map traversalEdge then u else 0 := by
  classical
  have hn := ((mem_candidates p q R ds).mp hds).2.1
  have hb := passageTime_le_candidate (Function.update w e u) p q R ds hds
  have he := trailCost_one_edge_change w (Function.update w e u) e
    (fun f hf => Function.update_of_ne hf _ _) p ds hn
  simp only [Function.update_self] at he
  unfold upward
  apply max_le
  · split_ifs at he ⊢ with hmem
    · linarith [hw e]
    · linarith
  · split_ifs <;> positivity

end GammaFPP.FiniteLocal

end OAI
