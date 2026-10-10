import OAI.Geometry.RCD.Metric.ModelVolumeComparison
import OAI.Geometry.RCD.Transport.CurvatureCompressionBound

namespace OAI

/-! # The canonical model parameter is small at bounded-curvature scales -/

open Set Metric
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.model_comparison_with_scale_control {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) :
    ∃ a : ℝ, 0 ≤ a ∧
      BallVolumeComparison (hausdorff n X) (comparisonModelVolume (n-1) a) ∧
      ∀ R : ℝ, 0 < R → -(1/9 : ℝ) ≤ K*R^2 → a*(3*R) ≤ 1 := by
  by_cases hK : 0 ≤ K
  · refine ⟨0,le_rfl,hX.zero_model_ballVolumeComparison hn hK,?_⟩
    intro R _ _
    simp
  · have hKneg : K < 0 := lt_of_not_ge hK
    refine ⟨Real.sqrt (-K/((n : ℝ)-1)),Real.sqrt_nonneg _,
      hX.negative_model_ballVolumeComparison hn hKneg,?_⟩
    intro R hR hcurv
    have hc3 : -1 ≤ K*(3*R)^2 := by nlinarith [hcurv]
    have hb := curvature_scaled_sqrt_le_one hn hKneg.le
      (mul_nonneg (by norm_num : (0:ℝ)≤3) hR.le) hc3
    simpa only [abs_of_neg hKneg,mul_comm] using hb

end RegularPointCoordinates

end

end OAI
