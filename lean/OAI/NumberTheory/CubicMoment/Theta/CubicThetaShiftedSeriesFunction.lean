import OAI.NumberTheory.CubicMoment.Theta.CubicThetaShiftedModelSeries
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaShiftedModelPeriodicity

namespace OAI

/-! The continuous periodic function given by the other-cusp arithmetic series. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaPeriodCell_coordinates (z : ℂ) :
    cubicThetaPeriodCell (cubicThetaPeriodCoordinates z)=z := by
  unfold cubicThetaPeriodCell cubicThetaPeriodCoordinates
  rw [ContinuousLinearEquiv.apply_symm_apply]
  field_simp

lemma cubicThetaShiftedModelSeries_torus (n : ℤ) {v : ℝ} (hv : 0<v) (z : ℂ) :
    cubicThetaShiftedModelSeries n (3*z) v=
      cubicThetaShiftedModelTorus n v
        (fun i => (cubicThetaPeriodCoordinates z i:UnitAddCircle)) := by
  have he := cubicThetaShiftedModelTorus_real n hv (cubicThetaPeriodCoordinates z)
  rw [cubicThetaPeriodCell_coordinates] at he
  exact he.symm

lemma cubicThetaShiftedModelSeries_continuous (n : ℤ) {v : ℝ} (hv : 0<v) :
    Continuous (fun z : ℂ => cubicThetaShiftedModelSeries n (3*z) v) := by
  simp_rw [cubicThetaShiftedModelSeries_torus n hv]
  apply (cubicThetaShiftedModelTorus n v).continuous.comp
  apply continuous_pi
  intro i
  exact (AddCircle.continuous_mk' (1:ℝ)).comp
    ((continuous_apply i).comp cubicThetaPeriodCoordinates_continuous)

lemma cubicThetaShifted_phase_tripled (z : ℂ) (h : Eisenstein) :
    (Real.fourierChar (tracePair (3*z) (cubicThetaShiftedRowFrequency h)):ℂ)=
      cubicThetaHorizontalCharacter h z := by
  unfold cubicThetaHorizontalCharacter
  apply congrArg (fun t : ℝ => (Real.fourierChar t:ℂ))
  rw [cubicThetaShiftedFrequency_third]
  exact congrArg (fun w : ℂ => 2*w.re) (by ring)

lemma cubicThetaShiftedModelSeries_periodic (n : ℤ) (v : ℝ) (m : Eisenstein) (z : ℂ) :
    cubicThetaShiftedModelSeries n (3*(z+3*(m:ℂ))) v=
      cubicThetaShiftedModelSeries n (3*z) v := by
  unfold cubicThetaShiftedModelSeries
  apply tsum_congr
  intro h
  rw [cubicThetaShifted_phase_tripled,cubicThetaShifted_phase_tripled,
    cubicThetaHorizontalCharacter_periodic]

lemma cubicThetaShifted_actual_continuous (b : Eisenstein) {v : ℝ} (hv : 0<v) :
    Continuous (fun z : ℂ => cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar
      (cubicThetaMobius (cubicThetaFullComplex (cubicThetaShiftedInversion b)) (3*z,v))) := by
  have hp : Continuous (fun z : ℂ => (⟨(3*z,v),hv⟩ : CubicThetaPoint)) :=
    ((continuous_const.mul continuous_id).prodMk continuous_const).subtype_mk _
  have hc := (cubicThetaArithmeticModel_point_continuous cubicThetaArithmeticBaseScalar).comp
    (continuous_const_smul (cubicThetaShiftedInversion b))
  have ht : Continuous (fun p : CubicThetaPoint =>
      cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar
        (cubicThetaMobius (cubicThetaFullComplex (cubicThetaShiftedInversion b)) p.val)) := by
    simpa only [Function.comp_def,cubicThetaFullPointAction_apply] using hc
  exact (ht.comp hp).congr (fun _ => rfl)

lemma cubicThetaShifted_actual_periodic (b m : Eisenstein) {v : ℝ} (hv : 0<v) (z : ℂ) :
    cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar
      (cubicThetaMobius (cubicThetaFullComplex (cubicThetaShiftedInversion b)) (3*(z+3*(m:ℂ)),v))=
    cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar
      (cubicThetaMobius (cubicThetaFullComplex (cubicThetaShiftedInversion b)) (3*z,v)) := by
  have he := cubicThetaShiftedModel_periodic b m (⟨(3*z,v),hv⟩ : CubicThetaPoint)
  change cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar
    (cubicThetaMobius (cubicThetaFullComplex (cubicThetaShiftedInversion b))
      (3*z+9*(m:ℂ),v))=_ at he
  rw [show 3*z+9*(m:ℂ)=3*(z+3*(m:ℂ)) by ring] at he
  exact he

end CubicFirstMoment

end

end OAI
