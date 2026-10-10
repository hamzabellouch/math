import Mathlib
import OAI.Analysis.RieszRectifiability.Limits.CompactLimitSupport

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped CompactlySupported

theorem compactTestConvergence_support_zero_of_first_moments {d : ℕ}
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, IsFiniteMeasureOnCompacts (μ j)] [IsFiniteMeasureOnCompacts ν]
    (hlocal : CompactTestConvergence μ ν) (q : Ambient d → ℝ) (hq : Continuous q)
    (hqnn : ∀ x, 0 ≤ q x)
    (hmoment : ∀ R : ℝ, 0 < R →
      Tendsto (fun j => ∫ x in ball (0 : Ambient d) R, q x ∂μ j) atTop (𝓝 0)) :
    ∀ x ∈ ν.support, q x = 0 := by
  intro x hx
  have hR : 0 < ‖x‖ + 2 := by positivity
  obtain ⟨f, hone, hzero, hcomp, hbounds⟩ := exists_continuous_one_zero_of_isCompact
    (isCompact_closedBall (0 : Ambient d) (‖x‖ + 1)) isOpen_ball.isClosed_compl
      (disjoint_compl_right_iff_subset.mpr (closedBall_subset_ball (by linarith : ‖x‖ + 1 < ‖x‖ + 2)))
  let F : C_c(Ambient d, ℝ) := ⟨⟨fun y => f y * q y, f.continuous.mul hq⟩, hcomp.mul_right⟩
  have hFnn : ∀ y, 0 ≤ F y := fun y => mul_nonneg (hbounds y).1 (hqnn y)
  have hbound : ∀ j, (∫ y, F y ∂μ j) ≤ ∫ y in ball (0 : Ambient d) (‖x‖ + 2), q y ∂μ j := by
    intro j
    have hi : IntegrableOn q (ball (0 : Ambient d) (‖x‖ + 2)) (μ j) :=
      (hq.continuousOn.integrableOn_compact
        (isCompact_closedBall (0 : Ambient d) (‖x‖ + 2))).mono_set ball_subset_closedBall
    rw [← integral_indicator measurableSet_ball]
    apply integral_mono (F.continuous.integrable_of_hasCompactSupport F.hasCompactSupport)
      (hi.integrable_indicator measurableSet_ball)
    intro y
    by_cases hy : y ∈ ball (0 : Ambient d) (‖x‖ + 2)
    · simpa only [indicator_of_mem hy, one_mul] using!
        mul_le_mul_of_nonneg_right (hbounds y).2 (hqnn y)
    · change f y * q y ≤ _
      rw [hzero hy, Pi.zero_apply, zero_mul, indicator_of_notMem hy]
  have hle : (∫ y, F y ∂ν) ≤ 0 := le_of_tendsto_of_tendsto
    (hlocal F) (hmoment (‖x‖ + 2) hR) (Filter.Eventually.of_forall hbound)
  have heq : (∫ y, F y ∂ν) = 0 := le_antisymm hle (integral_nonneg hFnn)
  have hae : F =ᵐ[ν] (fun _ => (0 : ℝ)) :=
    (integral_eq_zero_iff_of_nonneg_ae (Filter.Eventually.of_forall hFnn)
      (F.continuous.integrable_of_hasCompactSupport F.hasCompactSupport)).mp heq
  have hpoint := ν.support_subset_of_isClosed (isClosed_eq F.continuous continuous_const) hae hx
  change f x * q x = 0 at hpoint
  rw [hone (show x ∈ closedBall (0 : Ambient d) (‖x‖ + 1) by
    simp only [mem_closedBall, dist_zero_right]; linarith), Pi.one_apply, one_mul] at hpoint
  exact hpoint

end

end RieszRectifiability

end OAI
