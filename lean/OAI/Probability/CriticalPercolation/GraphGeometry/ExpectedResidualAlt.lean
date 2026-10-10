import Mathlib
import OAI.Probability.CriticalPercolation.Clusters.ExpectedCluster
import OAI.Probability.CriticalPercolation.Clusters.ComponentSelf
import OAI.Probability.CriticalPercolation.ProductMeasure.Distribution

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace CriticalPercolation.BondGraph
open CriticalPercolation.FiniteProduct CriticalPercolation.ClusterDeletion
open scoped Classical

variable {V E : Type*} [Fintype V] [Fintype E] (G : BondGraph V E)

lemma expectedResidual_alt (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (S : Set V) (s : V) (F : Set V → ℝ) (U : Set V) :
    G.expectedResidual w S s F U =
      expect w (fun ω => if s ∉ roots (delete (G.openGraph ω) U) S then
        G.expectedCluster w s F (roots (delete (G.openGraph ω) U) S) -
          F (component (delete (G.openGraph ω) U) s) else 0) := by
  have h := G.finite_spatialMarkov w hw S U
    (fun W H => if s ∉ W then G.expectedCluster w s F W -
      F (component (delete H U) s) else 0)
  have hdel : ∀ H W, delete (delete H W) U = delete H (W ∪ U) := by
    intro H W
    rw [delete_delete, Set.union_comm]
  simp_rw [hdel] at h
  have hleft : (fun ω : E → Prop => if s ∉ roots (delete (G.openGraph ω) U) S then
      G.expectedCluster w s F (roots (delete (G.openGraph ω) U) S) -
        F (component (delete (G.openGraph ω) (roots (delete (G.openGraph ω) U) S ∪ U)) s)
      else 0) =
      (fun ω => if s ∉ roots (delete (G.openGraph ω) U) S then
        G.expectedCluster w s F (roots (delete (G.openGraph ω) U) S) -
          F (component (delete (G.openGraph ω) U) s) else 0) := by
    funext ω
    split_ifs with hs
    · rfl
    · rw [delete_roots_union_component _ S U s hs]
  rw [hleft] at h
  erw [h]
  unfold expectedResidual
  congr 1
  funext ω
  split_ifs
  · rw [expect_zero]
  · rw [expect_sub, expect_const w hw]
    rfl

lemma later_cluster_residual (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (S : Set V) (s t : V) (F g : Set V → ℝ) (Q : Set V → Prop)
    (hQ : ∀ U, Q U → Disjoint U S ∧ s ∉ U) :
    (expect w (fun ω => if Q (component (G.openGraph ω) t) then
      if s ∉ roots (G.openGraph ω) S then
        g (component (G.openGraph ω) t) *
          (G.expectedCluster w s F (roots (G.openGraph ω) S) -
            F (component (G.openGraph ω) s)) else 0 else 0)) =
    expect w (fun ω => if Q (component (G.openGraph ω) t) then
      g (component (G.openGraph ω) t) *
        G.expectedResidual w S s F (component (G.openGraph ω) t) else 0) := by
  have h := G.finite_spatialMarkov w hw {t} ∅
    (fun U H => if Q U then if s ∉ roots H S then
      g U * (G.expectedCluster w s F (roots H S) - F (component H s)) else 0 else 0)
  simp only [delete_empty, roots_singleton] at h
  have hleft : (fun ω : E → Prop => if Q (component (G.openGraph ω) t) then
      if s ∉ roots (delete (G.openGraph ω) (component (G.openGraph ω) t)) S then
        g (component (G.openGraph ω) t) *
          (G.expectedCluster w s F (roots (delete (G.openGraph ω) (component (G.openGraph ω) t)) S) -
            F (component (delete (G.openGraph ω) (component (G.openGraph ω) t)) s))
        else 0 else 0) =
      (fun ω => if Q (component (G.openGraph ω) t) then
        if s ∉ roots (G.openGraph ω) S then
          g (component (G.openGraph ω) t) *
            (G.expectedCluster w s F (roots (G.openGraph ω) S) - F (component (G.openGraph ω) s))
          else 0 else 0) := by
    funext ω
    by_cases hq : Q (component (G.openGraph ω) t)
    · simp only [ite_eq_left hq]
      obtain ⟨hd, hs⟩ := hQ _ hq
      rw [roots_delete_component _ S t ((not_mem_roots_iff_disjoint _ S t).mpr hd),
        component_delete_component _ t s hs]
    · simp only [ite_eq_right hq]
  rw [hleft] at h
  erw [h]
  congr 1
  funext ω
  by_cases hq : Q (component (G.openGraph ω) t)
  · simp only [ite_eq_left hq]
    rw [G.expectedResidual_alt w hw]
    rw [← expect_const_mul]
    congr 1
    funext ω'
    split_ifs <;> simp
  · simp only [ite_eq_right hq, expect_zero]

end CriticalPercolation.BondGraph

end
end

end OAI
