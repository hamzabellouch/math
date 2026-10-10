import Mathlib
import OAI.Probability.CriticalPercolation.Clusters.ComponentSelf
import OAI.Probability.CriticalPercolation.Clusters.ExpectedCluster
import OAI.Probability.CriticalPercolation.ProductMeasure.Distribution

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace CriticalPercolation.BondGraph
open CriticalPercolation.FiniteProduct CriticalPercolation.ClusterDeletion

variable {V E : Type*} [Fintype V] [Fintype E] (G : BondGraph V E)

open scoped Classical

noncomputable def clusterUpdate (w : E → Prop → ℝ) (S : Set V) (s : V)
    (F : Set V → ℝ) (U : Set V) : ℝ :=
  expect w (fun ω => G.expectedCluster w s F (roots (delete (G.openGraph ω) U) S))

omit [Fintype V] in
lemma expectedCluster_antitone (w : E → Prop → ℝ) (hpos : ∀ e b, 0 ≤ w e b)
    (s : V) {F : Set V → ℝ} (hF : Monotone F) :
    Antitone (G.expectedCluster w s F) := by
  intro U U' hU
  exact expect_mono hpos fun ω => hF (component_mono (delete_antitone _ hU) s)

omit [Fintype V] in
lemma clusterUpdate_monotone (w : E → Prop → ℝ) (hpos : ∀ e b, 0 ≤ w e b)
    (S : Set V) (s : V) {F : Set V → ℝ} (hF : Monotone F) :
    Monotone (G.clusterUpdate w S s F) := by
  intro U U' hU
  exact expect_mono hpos fun ω => G.expectedCluster_antitone w hpos s hF
    (roots_mono (delete_antitone _ hU) S)

omit [Fintype V] in
lemma clusterUpdate_nonneg (w : E → Prop → ℝ) (hpos : ∀ e b, 0 ≤ w e b)
    (S : Set V) (s : V) {F : Set V → ℝ} (hF : ∀ U, 0 ≤ F U) (U : Set V) :
    0 ≤ G.clusterUpdate w S s F U :=
  expect_nonneg hpos fun _ => expect_nonneg hpos fun _ => hF _

noncomputable def avoidedAverage (w : E → Prop → ℝ) (S : Set V) (s : V)
    (F : Set V → ℝ) : ℝ := by
  classical
  exact expect w (fun ω => if s ∉ roots (G.openGraph ω) S then
    F (component (G.openGraph ω) s) else 0)

lemma clusterUpdate_exposure (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (S : Set V) (s : V) (F g : Set V → ℝ) :
    (expect w (fun ω => if s ∉ roots (G.openGraph ω) S then
      g (component (G.openGraph ω) s) * G.expectedCluster w s F (roots (G.openGraph ω) S)
      else 0)) =
    G.avoidedAverage w S s (fun U => g U * G.clusterUpdate w S s F U) := by
  classical
  have h := G.finite_spatialMarkov w hw {s} ∅
    (fun U H => if Disjoint U S then g U * G.expectedCluster w s F (roots H S) else 0)
  simp only [delete_empty, roots_singleton] at h
  have hleft : (fun ω : E → Prop =>
      if Disjoint (component (G.openGraph ω) s) S then
        g (component (G.openGraph ω) s) * G.expectedCluster w s F
          (roots (delete (G.openGraph ω) (component (G.openGraph ω) s)) S) else 0) =
      (fun ω => if s ∉ roots (G.openGraph ω) S then
        g (component (G.openGraph ω) s) * G.expectedCluster w s F
          (roots (G.openGraph ω) S) else 0) := by
    funext ω
    rw [← not_mem_roots_iff_disjoint]
    split_ifs with hs
    · rfl
    · rw [roots_delete_component _ S s hs]
  rw [hleft] at h
  erw [h]
  unfold avoidedAverage
  congr 1
  funext ω
  rw [← not_mem_roots_iff_disjoint]
  split_ifs
  · rw [expect_zero]
  · rw [expect_const_mul]
    rfl

lemma avoidedAverage_exposure (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (S : Set V) (s : V) (F : Set V → ℝ) :
    G.avoidedAverage w S s F =
      expect w (fun ω => if s ∉ roots (G.openGraph ω) S then
        G.expectedCluster w s F (roots (G.openGraph ω) S) else 0) := by
  classical
  have h := G.finite_spatialMarkov w hw S ∅
    (fun W H => if s ∉ W then F (component H s) else 0)
  simp only [delete_empty] at h
  have hleft : (fun ω : E → Prop => if s ∉ roots (G.openGraph ω) S then
      F (component (delete (G.openGraph ω) (roots (G.openGraph ω) S)) s) else 0) =
      (fun ω => if s ∉ roots (G.openGraph ω) S then F (component (G.openGraph ω) s) else 0) := by
    funext ω
    split_ifs with hs
    · rfl
    · rw [delete_roots_component _ S s hs]
  rw [hleft] at h
  change expect w _ = _
  erw [h]
  congr 1
  funext ω
  split_ifs
  · rw [expect_zero]
  · rfl

lemma clusterUpdate_stationary (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (S : Set V) (s : V) (F : Set V → ℝ) :
    G.avoidedAverage w S s (G.clusterUpdate w S s F) = G.avoidedAverage w S s F := by
  have h := G.clusterUpdate_exposure w hw S s F (fun _ => 1)
  simp only [one_mul] at h
  exact h.symm.trans (G.avoidedAverage_exposure w hw S s F).symm

end CriticalPercolation.BondGraph

end
end

end OAI
