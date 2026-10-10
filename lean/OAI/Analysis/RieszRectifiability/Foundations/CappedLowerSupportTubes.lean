import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.CappedLowerGrowth
import OAI.Analysis.RieszRectifiability.Limits.CompactReverseSupportTube

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

theorem compactTestConvergence_capped_support_tube {d : ℕ} (n : ℕ) (C H : ℝ)
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, IsFiniteMeasureOnCompacts (μ j)] [IsFiniteMeasureOnCompacts ν]
    (hlocal : CompactTestConvergence μ ν) (hC : 0 < C) (hH : 0 < H)
    (hlower : ∀ j, CappedLowerGrowth n C H (μ j)) (a : Ambient d)
    (R ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ j in atTop, ∀ x ∈ ball a R, x ∈ (μ j).support → infDist x ν.support < ε := by
  let r := min (ε / 2) H
  have hr : 0 < r := lt_min (half_pos hε) hH
  have hzero : ∀ᵐ x ∂ν, infDist x ν.support = 0 := by
    filter_upwards [ν.support_mem_ae] with x hx
    exact infDist_zero_of_mem hx
  apply compactTestConvergence_support_tube μ ν hlocal (fun x => infDist x ν.support)
    1 (lipschitz_infDist_pt ν.support) hzero a R ε r (r ^ n / C) hε (by positivity)
    (by simpa only [NNReal.coe_one, one_mul] using! min_le_left (ε / 2) H)
  exact Eventually.of_forall fun j x _ hx =>
    CappedLowerGrowth.real_bound n C H (μ j) hC (hlower j) x hx r hr (min_le_right _ _)

theorem compactTestConvergence_capped_bilateral_tubes {d : ℕ} (n : ℕ) (C H : ℝ)
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, IsFiniteMeasureOnCompacts (μ j)] [IsFiniteMeasureOnCompacts ν]
    (hlocal : CompactTestConvergence μ ν) (hC : 0 < C) (hH : 0 < H)
    (hlower : ∀ j, CappedLowerGrowth n C H (μ j)) (a : Ambient d)
    (R ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ j in atTop,
      (∀ x ∈ ball a R, x ∈ (μ j).support → infDist x ν.support < ε) ∧
      (∀ x ∈ ball a R, x ∈ ν.support → infDist x (μ j).support < ε) :=
  (compactTestConvergence_capped_support_tube n C H μ ν hlocal hC hH hlower a R ε hε).and
    (compactTestConvergence_reverse_support_tube μ ν hlocal a R ε hε)

end

end RieszRectifiability

end OAI
