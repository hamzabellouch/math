import OAI.Geometry.RCD.Metric.LowerCurvatureVolume
import OAI.Geometry.RCD.Metric.ComparisonModel

namespace OAI

/-! # The flat volume comparison from nonnegative CD curvature -/

open Set Metric MeasureTheory

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem NoncollapsedRCD.flat_ballVolumeComparison {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) (hK : 0 ≤ K) :
    BallVolumeComparison (hausdorff n X) (fun r => r ^ n) := by
  let := hX.separable
  let := locallyFinite_of_finiteOnBounded (hausdorff n X) hX.finiteOnBounded
  intro p r R hr hrR
  have hR : 0 < R := hr.trans_le hrR
  have h := hX.cd.nonneg_ball_ratio (hausdorff n X) K n hX.fullSupport
    hX.finiteOnBounded hn hK p r R hr hrR
  have hreal := ENNReal.toReal_mono (hX.finiteOnBounded (ball p r) isBounded_ball).ne h
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal (div_pos hr hR).le] at hreal
  change (r / R) ^ n * (hausdorff n X).real (ball p R) ≤
    (hausdorff n X).real (ball p r) at hreal
  calc
    (hausdorff n X).real (ball p R) * r ^ n =
        ((r / R) ^ n * (hausdorff n X).real (ball p R)) * R ^ n := by
      rw [div_pow]
      field_simp
    _ ≤ (hausdorff n X).real (ball p r) * R ^ n :=
      mul_le_mul_of_nonneg_right hreal (pow_nonneg hR.le _)

theorem NoncollapsedRCD.zero_model_ballVolumeComparison {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) (hK : 0 ≤ K) :
    BallVolumeComparison (hausdorff n X) (comparisonModelVolume (n - 1) 0) := by
  intro p r R hr hrR
  simpa only [comparisonModelVolume_zero, Nat.sub_add_cancel (by omega : 1 ≤ n)] using
    hX.flat_ballVolumeComparison hn hK p r R hr hrR

end RegularPointCoordinates

end OAI
