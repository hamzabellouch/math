import OAI.Analysis.RCDHeat.Foundations

namespace OAI

/-! # Image bounds for the exact normalized Hausdorff measure

The normalization factor is the same in source and target. This does not
identify the Euclidean target measure with Lebesgue measure.
-/

open Set Metric MeasureTheory
open scoped ENNReal NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]

theorem normalized_hausdorff_image_le {n : ℕ} {C : ℝ≥0} {u : X → Y} {A : Set X}
    (hu : LipschitzOnWith C u A) :
    hausdorff n Y (u '' A) ≤ (C : ℝ≥0∞)^n * hausdorff n X A := by
  have hh := hu.hausdorffMeasure_image_le (d := (n:ℝ)) (by positivity)
  rw [ENNReal.rpow_natCast] at hh
  simp only [hausdorff,Measure.smul_apply,smul_eq_mul]
  calc
    _ ≤ (volume (ball (0 : Euclidean n) 1)/(2:ℝ≥0∞)^n)*
        ((C:ℝ≥0∞)^n*Measure.hausdorffMeasure (n:ℝ) A) := mul_le_mul' le_rfl hh
    _ = _ := by ac_rfl

theorem normalized_hausdorff_real_image_le {n : ℕ} {C : ℝ≥0} {u : X → Y} {A : Set X}
    (hu : LipschitzOnWith C u A) (hA : hausdorff n X A ≠ ⊤) :
    (hausdorff n Y).real (u '' A) ≤ (C:ℝ)^n*(hausdorff n X).real A := by
  have hh := ENNReal.toReal_mono (ENNReal.mul_ne_top
    (ENNReal.pow_ne_top ENNReal.coe_ne_top) hA) (normalized_hausdorff_image_le hu)
  simpa only [ENNReal.toReal_mul,ENNReal.toReal_pow,ENNReal.coe_toReal,Measure.real] using hh

end RegularPointCoordinates

end

end OAI
