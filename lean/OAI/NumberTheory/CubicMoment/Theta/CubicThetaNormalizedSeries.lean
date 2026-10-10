import OAI.NumberTheory.CubicMoment.Theta.CubicThetaArithmeticModelInversion

namespace OAI

/-! Normalize the actual automorphic function by its nonzero Fourier
coefficient. Its constant coefficient is retained explicitly. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaSeriesConstant : ℂ :=
  (cubicThetaConstant:ℂ)/cubicThetaArithmeticBaseScalar

def cubicThetaNormalizedSeriesSection : CubicThetaSection :=
  cubicThetaArithmeticBaseScalar⁻¹ • cubicThetaArithmeticModelSection

lemma cubicThetaNormalizedSeriesSection_apply (p : CubicThetaPoint) :
    cubicThetaNormalizedSeriesSection.val p=
      cubicThetaSeriesConstant*((p.val.2^(2/3:ℝ):ℝ):ℂ)+
        cubicThetaNonconstant cubicThetaArithmeticCoefficient p.val := by
  change cubicThetaArithmeticBaseScalar⁻¹*
    cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar p.val=_
  unfold cubicThetaArithmeticModel cubicThetaSeriesConstant
  push_cast
  field_simp [cubicThetaArithmeticBaseScalar_ne_zero]

theorem cubicThetaNormalizedSeriesSection_inversion (p : CubicThetaPoint) :
    cubicThetaNormalizedSeriesSection.val (cubicThetaFullInversion • p)=
      cubicThetaNormalizedSeriesSection.val p := by
  change cubicThetaArithmeticBaseScalar⁻¹*
    cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar (cubicThetaFullInversion • p).val=_
  rw [cubicThetaArithmeticModel_inversion]
  rfl

theorem cubicThetaArithmetic_center_inversion {v : ℝ} (hv : 0<v) :
    cubicThetaNonconstant cubicThetaArithmeticCoefficient (0,v⁻¹)=
      cubicThetaNonconstant cubicThetaArithmeticCoefficient (0,v)+
        cubicThetaSeriesConstant*(((v^(2/3:ℝ):ℝ):ℂ)-(((v⁻¹)^(2/3:ℝ):ℝ):ℂ)) := by
  let p : CubicThetaPoint := ⟨(0,v),hv⟩
  have he := cubicThetaNormalizedSeriesSection_inversion p
  rw [cubicThetaNormalizedSeriesSection_apply (cubicThetaFullInversion • p),
    cubicThetaNormalizedSeriesSection_apply p] at he
  change cubicThetaSeriesConstant*
      (((cubicThetaMobius (cubicThetaFullComplex cubicThetaFullInversion) (0,v)).2^(2/3:ℝ):ℝ):ℂ)+
    cubicThetaNonconstant cubicThetaArithmeticCoefficient
      (cubicThetaMobius (cubicThetaFullComplex cubicThetaFullInversion) (0,v))=_ at he
  rw [cubicThetaFullInversion_complex,cubicThetaMobius_inversion one_ne_zero hv,
    cubicThetaInversion_center 1 hv] at he
  norm_num only [map_one,one_mul] at he
  linear_combination he

theorem cubicThetaArithmetic_center_small {v : ℝ} (hv : 0<v) :
    cubicThetaNonconstant cubicThetaArithmeticCoefficient (0,v)=
      cubicThetaNonconstant cubicThetaArithmeticCoefficient (0,v⁻¹)+
        cubicThetaSeriesConstant*((((v⁻¹)^(2/3:ℝ):ℝ):ℂ)-((v^(2/3:ℝ):ℝ):ℂ)) := by
  have he := cubicThetaArithmetic_center_inversion hv
  linear_combination -he

end CubicFirstMoment

end

end OAI
