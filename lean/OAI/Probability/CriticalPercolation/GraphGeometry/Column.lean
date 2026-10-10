import Mathlib
import OAI.Probability.CriticalPercolation.Clusters.ClusterUpdate
import OAI.Probability.CriticalPercolation.Clusters.Earlier
import OAI.Probability.CriticalPercolation.GraphGeometry.ExpectedResidualAlt

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace CriticalPercolation.BondGraph
open CriticalPercolation.FiniteProduct CriticalPercolation.ClusterDeletion
open CriticalPercolation.ClusterColumns
open scoped Classical

variable {V E : Type*} [Fintype V] [Fintype E] (G : BondGraph V E)

lemma avoided_drift_zero (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (S : Set V) (s : V) (F b : Set V → ℝ) :
    expect w (fun ω => if s ∉ roots (G.openGraph ω) S then
      b (roots (G.openGraph ω) S) * (F (component (G.openGraph ω) s) -
        G.expectedCluster w s F (roots (G.openGraph ω) S)) else 0) = 0 := by
  have h := G.finite_spatialMarkov w hw S ∅
    (fun W H => if s ∉ W then b W * (F (component H s) - G.expectedCluster w s F W) else 0)
  simp only [delete_empty] at h
  have hleft : (fun ω : E → Prop => if s ∉ roots (G.openGraph ω) S then
      b (roots (G.openGraph ω) S) * (F (component (delete (G.openGraph ω) (roots (G.openGraph ω) S)) s) -
        G.expectedCluster w s F (roots (G.openGraph ω) S)) else 0) =
      (fun ω => if s ∉ roots (G.openGraph ω) S then
        b (roots (G.openGraph ω) S) * (F (component (G.openGraph ω) s) -
          G.expectedCluster w s F (roots (G.openGraph ω) S)) else 0) := by
    funext ω
    split_ifs with hs
    · rfl
    · rw [delete_roots_component _ S s hs]
  rw [hleft] at h
  erw [h]
  have hz : ∀ W : Set V, expect w (fun ω => if s ∉ W then
      b W * (F (component (delete (G.openGraph ω) W) s) - G.expectedCluster w s F W)
      else 0) = 0 := by
    intro W
    split_ifs
    · exact expect_zero w
    · rw [expect_const_mul, expect_sub, expect_const w hw]
      change b W * (G.expectedCluster w s F W - G.expectedCluster w s F W) = 0
      ring
  simp only [hz, expect_zero]

noncomputable def column {n : ℕ} (w : E → Prop → ℝ) (x : Fin n → V)
    (k : Fin n) (F : Set V → ℝ) (i : Fin n) : ℝ :=
  expect w (fun ω => select (G.openGraph ω) x k i * F (component (G.openGraph ω) (x k)))

omit [Fintype V] in
lemma column_as_avoidedAverage {n : ℕ} (w : E → Prop → ℝ) (x : Fin n → V)
    (k : Fin n) (F : Set V → ℝ) (i : Fin n) :
    G.column w x k F i = G.avoidedAverage w (earlier x k) (x k)
      (fun U => (if x i ∈ U then 1 else 0) * F U) := by
  unfold column avoidedAverage select first
  congr 1
  funext ω
  split_ifs <;> simp_all

lemma column_update {n : ℕ} (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (x : Fin n → V) (k : Fin n) (F : Set V → ℝ) (i : Fin n) :
    G.column w x k (G.clusterUpdate w (earlier x k) (x k) F) i =
      expect w (fun ω => select (G.openGraph ω) x k i *
        G.expectedCluster w (x k) F (roots (G.openGraph ω) (earlier x k))) := by
  rw [G.column_as_avoidedAverage]
  rw [← G.clusterUpdate_exposure w hw]
  congr 1
  funext ω
  simp only [select, first]
  split_ifs <;> simp_all

lemma column_later_residual {n : ℕ} (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (x : Fin n → V) {k l : Fin n} (hkl : k < l) (F : Set V → ℝ) (i : Fin n) :
    G.column w x l (G.expectedResidual w (earlier x k) (x k) F) i =
    expect w (fun ω => if first (G.openGraph ω) x k then
      select (G.openGraph ω) x l i *
        (G.expectedCluster w (x k) F (roots (G.openGraph ω) (earlier x k)) -
          F (component (G.openGraph ω) (x k))) else 0) := by
  have h := G.later_cluster_residual w hw (earlier x k) (x k) (x l) F
    (fun U => if x i ∈ U then 1 else 0) (fun U => Disjoint U (earlier x l))
    (fun U hU => ⟨hU.mono_right (earlier_mono x hkl.le),
      fun hs => (Set.disjoint_left.mp hU) hs ⟨k, hkl, rfl⟩⟩)
  have hc : (fun ω : E → Prop => if Disjoint (component (G.openGraph ω) (x l)) (earlier x l) then
      (if x i ∈ component (G.openGraph ω) (x l) then 1 else 0) *
        G.expectedResidual w (earlier x k) (x k) F (component (G.openGraph ω) (x l)) else 0) =
      (fun ω => select (G.openGraph ω) x l i *
        G.expectedResidual w (earlier x k) (x k) F (component (G.openGraph ω) (x l))) := by
    funext ω
    simp only [select, first, not_mem_roots_iff_disjoint]
    split_ifs <;> simp_all
  rw [hc] at h
  unfold column
  erw [← h]
  congr 1
  funext ω
  simp only [select, first, not_mem_roots_iff_disjoint]
  split_ifs <;> simp_all

lemma column_decomposition {n : ℕ} (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (x : Fin n → V) (k : Fin n) (F : Set V → ℝ) (i : Fin n) :
    G.column w x k F i =
      G.column w x k (G.clusterUpdate w (earlier x k) (x k) F) i +
        ∑ l, if k < l then G.column w x l (G.expectedResidual w (earlier x k) (x k) F) i else 0 := by
  have hzero := G.avoided_drift_zero w hw (earlier x k) (x k) F
    (fun W => if x i ∉ W then 1 else 0)
  have hpoint : (fun ω : E → Prop => if x k ∉ roots (G.openGraph ω) (earlier x k) then
      (if x i ∉ roots (G.openGraph ω) (earlier x k) then (1 : ℝ) else 0) *
        (F (component (G.openGraph ω) (x k)) -
          G.expectedCluster w (x k) F (roots (G.openGraph ω) (earlier x k))) else 0) =
      (fun ω => select (G.openGraph ω) x k i *
        (F (component (G.openGraph ω) (x k)) -
          G.expectedCluster w (x k) F (roots (G.openGraph ω) (earlier x k))) -
        ∑ l, if k < l then if first (G.openGraph ω) x k then
          select (G.openGraph ω) x l i *
            (G.expectedCluster w (x k) F (roots (G.openGraph ω) (earlier x k)) -
              F (component (G.openGraph ω) (x k))) else 0 else 0) := by
    funext ω
    by_cases hk : first (G.openGraph ω) x k
    · simp only [show x k ∉ roots (G.openGraph ω) (earlier x k) from hk,
        not_false_eq_true, ite_true]
      rw [select_truncation]
      simp only [hk, ite_true]
      have hsum : ∀ a : ℝ,
          (∑ l, if k < l then select (G.openGraph ω) x l i * a else 0) =
          (∑ l, if k < l then select (G.openGraph ω) x l i else 0) * a := by
        intro a
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro l _
        split_ifs <;> simp
      rw [hsum]
      ring
    · have hk' : ¬ (x k ∉ roots (G.openGraph ω) (earlier x k)) := hk
      simp [hk', hk, select]
  rw [hpoint] at hzero
  erw [expect_sub, expect_sum] at hzero
  have hlater : (∑ l, expect w (fun ω => if k < l then if first (G.openGraph ω) x k then
          select (G.openGraph ω) x l i *
            (G.expectedCluster w (x k) F (roots (G.openGraph ω) (earlier x k)) -
              F (component (G.openGraph ω) (x k))) else 0 else 0)) =
      ∑ l, if k < l then G.column w x l (G.expectedResidual w (earlier x k) (x k) F) i else 0 := by
    apply Finset.sum_congr rfl
    intro l _
    by_cases hkl : k < l
    · simp only [hkl, ite_true]
      exact (G.column_later_residual w hw x hkl F i).symm
    · simp only [hkl, ite_false, expect_zero]
  erw [hlater] at hzero
  have hdiff : G.column w x k F i -
      G.column w x k (G.clusterUpdate w (earlier x k) (x k) F) i =
      expect w (fun ω => select (G.openGraph ω) x k i *
        (F (component (G.openGraph ω) (x k)) -
          G.expectedCluster w (x k) F (roots (G.openGraph ω) (earlier x k)))) := by
    rw [G.column_update w hw]
    unfold column
    erw [← expect_sub]
    congr 1
    funext ω
    ring
  exact sub_eq_iff_eq_add'.mp (hdiff.trans (sub_eq_zero.mp hzero))

end CriticalPercolation.BondGraph

end
end

end OAI
