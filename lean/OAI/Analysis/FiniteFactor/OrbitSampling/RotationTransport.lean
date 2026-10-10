import OAI.Analysis.FiniteFactor.OrbitSampling.Measures

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped Classical ENNReal
noncomputable section

theorem coordinateRotate_neg_cube (θ x : SourceCoordinate → ℝ) (n : ℤ)
    (hx : ∀ i, x i ∈ Set.Ico (0 : ℝ) 1) :
    coordinateRotate θ (-n) (coordinateRotate θ n x) = x := by
  funext i
  unfold coordinateRotate
  rw [Int.cast_neg,neg_mul]
  have he : Int.fract (x i+(n : ℝ)*θ i) + -((n : ℝ)*θ i) =
      x i - (⌊x i+(n : ℝ)*θ i⌋ : ℝ) := by
    linarith [Int.fract_add_floor (x i+(n : ℝ)*θ i)]
  rw [he,Int.fract_sub_intCast,Int.fract_eq_self.mpr (hx i)]

theorem coordinateRotate_phase (θ x : SourceCoordinate → ℝ) (n : ℤ) (i : SourceCoordinate) :
    coordinateRotate θ n x i = Int.fract (x i+Int.fract ((n : ℝ)*θ i)) := by
  unfold coordinateRotate
  have he : x i+(n : ℝ)*θ i = (x i+Int.fract ((n : ℝ)*θ i)) + (⌊(n : ℝ)*θ i⌋ : ℝ) := by
    linarith [Int.fract_add_floor ((n : ℝ)*θ i)]
  rw [he,Int.fract_add_intCast]

theorem coordinateRotate_neg_phase (θ x : SourceCoordinate → ℝ) (n : ℤ) (i : SourceCoordinate) :
    coordinateRotate θ (-n) x i = Int.fract (x i-Int.fract ((n : ℝ)*θ i)) := by
  unfold coordinateRotate
  rw [Int.cast_neg,neg_mul]
  have he : x i + -((n : ℝ)*θ i) = (x i-Int.fract ((n : ℝ)*θ i)) - (⌊(n : ℝ)*θ i⌋ : ℝ) := by
    linarith [Int.fract_add_floor ((n : ℝ)*θ i)]
  rw [he,Int.fract_sub_intCast]

/-- Change of variables for an actual weighted Haar law. The inverse identity
is needed only on the conull cube of representatives. -/
theorem sourceSamplingHaar_rotate_withDensity (θ : SourceCoordinate → ℝ) (n : ℤ)
    (w : (SourceCoordinate → ℝ) → ℝ≥0∞) (hw : Measurable w) :
    (sourceSamplingHaar.withDensity w).map (coordinateRotate θ n) =
      sourceSamplingHaar.withDensity (fun y => w (coordinateRotate θ (-n) y)) := by
  let R := coordinateRotate θ n
  let R' := coordinateRotate θ (-n)
  have hR := coordinateRotate_preserving θ n
  have hR' := coordinateRotate_preserving θ (-n)
  ext A hA
  rw [Measure.map_apply hR.measurable hA,withDensity_apply _ (hR.measurable hA),withDensity_apply _ hA]
  rw [← lintegral_indicator (hR.measurable hA),← lintegral_indicator hA]
  have hm : Measurable (A.indicator (fun y => w (R' y))) := (hw.comp hR'.measurable).indicator hA
  calc
    _ = ∫⁻ x, A.indicator (fun y => w (R' y)) (R x) ∂sourceSamplingHaar := by
      apply lintegral_congr_ae
      filter_upwards [sourceSamplingHaar_cube] with x hx
      change (if R x ∈ A then w x else 0) = (if R x ∈ A then w (R' (R x)) else 0)
      rw [show R' (R x) = x from coordinateRotate_neg_cube θ x n hx]
    _ = _ := hR.lintegral_comp hm

end
end FiniteFactor

end OAI
