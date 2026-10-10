import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.KernelBasic
import OAI.Analysis.RieszRectifiability.Flatness.PlaneDiskHausdorffMeasure

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal Pointwise

theorem ambient_closedBall_hausdorffMeasure (n : ℕ) (a : Ambient n)
    (r : ℝ) (hr : 0 < r) :
    (μH[(n : ℝ)] : Measure (Ambient n)) (closedBall a r) =
      (ENNReal.ofReal r) ^ n * planeUnitHausdorffMeasure n := by
  have hd : 0 ≤ (n : ℝ) := by positivity
  have htranslate := (IsometryEquiv.addRight a).isometry.hausdorffMeasure_image
    (Or.inl hd) (closedBall (0 : Ambient n) r)
  rw [(IsometryEquiv.addRight a).image_closedBall] at htranslate
  change (μH[(n : ℝ)] : Measure (Ambient n)) (closedBall (0 + a) r) = _ at htranslate
  rw [zero_add] at htranslate
  rw [htranslate]
  have hscale := Measure.hausdorffMeasure_smul₀ (𝕜 := ℝ) hd hr.ne'
    (closedBall (0 : Ambient n) 1)
  have hnorm : (‖r‖₊ : ℝ≥0∞) = ENNReal.ofReal r := by
    rw [← Real.toNNReal_eq_nnnorm_of_nonneg hr.le]
    rfl
  simpa only [smul_closedBall' hr.ne', smul_zero, Real.norm_of_nonneg hr.le,
    mul_one, NNReal.rpow_natCast, ENNReal.smul_def, smul_eq_mul,
    ENNReal.coe_pow, hnorm, planeUnitHausdorffMeasure] using! hscale

theorem native_hausdorff_global_upper_growth (n : ℕ) :
    GlobalUpperGrowth n (planeUnitHausdorffMeasure n).toReal
      (μH[(n : ℝ)] : Measure (Ambient n)) := by
  refine ⟨ENNReal.toReal_nonneg, ?_⟩
  intro x r hr
  have hbound := measure_mono (ball_subset_closedBall (x := x) (ε := r))
    (μ := (μH[(n : ℝ)] : Measure (Ambient n)))
  rw [ambient_closedBall_hausdorffMeasure n x r hr] at hbound
  convert! hbound using 1
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal (planeUnitHausdorffMeasure_lt_top n).ne,
    ENNReal.ofReal_pow hr.le]
  exact mul_comm _ _

end

end RieszRectifiability

end OAI
