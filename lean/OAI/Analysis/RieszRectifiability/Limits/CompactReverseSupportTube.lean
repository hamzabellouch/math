import Mathlib
import OAI.Analysis.RieszRectifiability.Limits.CompactLimitSupport

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

theorem compactTestConvergence_compact_reverse_support_tube {d : ℕ}
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, IsFiniteMeasureOnCompacts (μ j)] [IsFiniteMeasureOnCompacts ν]
    (hlocal : CompactTestConvergence μ ν) (K : Set (Ambient d)) (hK : IsCompact K)
    (hsub : K ⊆ ν.support) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ j in atTop, ∀ x ∈ K, infDist x (μ j).support < ε := by
  classical
  have hh : 0 < ε / 2 := half_pos hε
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover (fun y : K => ball (y : Ambient d) (ε / 2))
    (fun _ => isOpen_ball) (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, mem_ball_self hh⟩)
  have hnear : ∀ᶠ j in atTop, ∀ y ∈ s,
      ∃ z, z ∈ (μ j).support ∧ z ∈ ball (y : Ambient d) (ε / 2) := by
    apply (Filter.eventually_all_finset s).mpr
    intro y _hy
    exact compactTestConvergence_nearby_support μ ν hlocal y (hsub y.property) (ε / 2) hh
  filter_upwards [hnear] with j hj
  intro x hx
  obtain ⟨y, hy⟩ := mem_iUnion.mp (hs hx)
  obtain ⟨hys, hxy⟩ := mem_iUnion.mp hy
  obtain ⟨z, hz, hzy⟩ := hj y hys
  have hdist : dist x z < ε := by
    have h1 : dist x (y : Ambient d) < ε / 2 := hxy
    have h2 : dist (y : Ambient d) z < ε / 2 := by simpa only [dist_comm] using! hzy
    exact (dist_triangle x (y : Ambient d) z).trans_lt (by linarith)
  exact (infDist_le_dist_of_mem hz).trans_lt hdist

theorem compactTestConvergence_reverse_support_tube {d : ℕ}
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, IsFiniteMeasureOnCompacts (μ j)] [IsFiniteMeasureOnCompacts ν]
    (hlocal : CompactTestConvergence μ ν) (a : Ambient d) (R ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ j in atTop, ∀ x ∈ ball a R, x ∈ ν.support → infDist x (μ j).support < ε := by
  have hK : IsCompact (ν.support ∩ closedBall a R) :=
    (isCompact_closedBall a R).inter_left ν.isClosed_support
  filter_upwards [compactTestConvergence_compact_reverse_support_tube μ ν hlocal
    (ν.support ∩ closedBall a R) hK inter_subset_left ε hε] with j hj
  intro x hx hs
  exact hj x ⟨hs, ball_subset_closedBall hx⟩

end

end RieszRectifiability

end OAI
