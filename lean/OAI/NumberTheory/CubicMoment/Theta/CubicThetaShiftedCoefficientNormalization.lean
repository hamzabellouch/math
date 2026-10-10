import OAI.NumberTheory.CubicMoment.Theta.CubicThetaShiftedWhittaker
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCoefficientScalar

namespace OAI

/-! The other-cusp Whittaker coefficients have the explicit arithmetic
normalization, with the same actual scalar as the original cusp. -/
noncomputable section
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

lemma cubicThetaShiftedFrequency_lambda (h : Eisenstein) :
    cubicThetaRowFrequency (lambdaE*h)=
      (3*traceLambda)*cubicThetaShiftedRowFrequency h := by
  unfold cubicThetaRowFrequency cubicThetaShiftedRowFrequency
  push_cast
  rw [lambdaE_coe]
  field_simp [traceLambda_ne_zero]
  ring

lemma cubicThetaShiftedPoleWeight {h : Eisenstein} (hh : h≠0) :
    2*(cubicThetaShiftedRowHeatScale h)^(1/6:ℝ)/‖cubicThetaShiftedRowFrequency h‖=
      3*(2*(cubicThetaRowHeatScale (lambdaE*h))^(1/6:ℝ)/
        ‖cubicThetaRowFrequency (lambdaE*h)‖) := by
  have hl : ‖traceLambda‖=Real.sqrt 3 := by
    apply (sq_eq_sq₀ (_root_.norm_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [←Complex.normSq_eq_norm_sq,traceLambda_normSq,Real.sq_sqrt (by norm_num)]
  have hq : ‖cubicThetaRowFrequency (lambdaE*h)‖=
      3*Real.sqrt 3*‖cubicThetaShiftedRowFrequency h‖ := by
    rw [cubicThetaShiftedFrequency_lambda,norm_mul,norm_mul,Complex.norm_ofNat,hl]
  have hA : cubicThetaRowHeatScale (lambdaE*h)=27*cubicThetaShiftedRowHeatScale h := by
    unfold cubicThetaRowHeatScale cubicThetaShiftedRowHeatScale
    rw [cubicThetaShiftedFrequency_lambda,Complex.normSq_mul,Complex.normSq_mul,
      traceLambda_normSq]
    norm_num
    ring
  have h27 : (27:ℝ)^(1/6:ℝ)=Real.sqrt 3 := by
    calc
      _ = ((3:ℝ)^3)^(1/6:ℝ) := by norm_num
      _ = (3:ℝ)^((3:ℝ)*(1/6:ℝ)) := by
        rw [←Real.rpow_natCast,←Real.rpow_mul (by norm_num : (0:ℝ)≤3)]
        norm_num
      _ = (3:ℝ)^(1/2:ℝ) := by norm_num
      _ = Real.sqrt 3 := (Real.sqrt_eq_rpow 3).symm
  have hn : ‖cubicThetaShiftedRowFrequency h‖≠0 := norm_ne_zero_iff.mpr (by
    unfold cubicThetaShiftedRowFrequency
    exact div_ne_zero (fun hz => hh (Subtype.ext hz)) (mul_ne_zero (by norm_num) traceLambda_ne_zero))
  rw [hA,Real.mul_rpow (by norm_num) (cubicThetaShiftedRowHeatScale_pos hh).le,h27,hq]
  field_simp

def cubicThetaShiftedNormalizedCoefficient (n : ℤ) (h : Eisenstein) : ℂ :=
  (cubicThetaShiftedResidueFactor n h*
    ((2*(cubicThetaShiftedRowHeatScale h)^(1/6:ℝ)/‖cubicThetaShiftedRowFrequency h‖:ℝ):ℂ))/
    ((81*Real.sqrt 3/2:ℝ):ℂ)

theorem cubicThetaShiftedNormalizedCoefficient_explicit (n : ℤ) {h : Eisenstein} (hh : h≠0) :
    cubicThetaShiftedNormalizedCoefficient n h=
      if (3:Eisenstein) ∣ h-lambdaE*(n:Eisenstein) then
        3*cubicThetaArithmeticBaseScalar*cubicThetaArithmeticCoefficient (3*h) else 0 := by
  unfold cubicThetaShiftedNormalizedCoefficient cubicThetaShiftedResidueFactor
  rw [cubicThetaRegularizedShiftedFrequency_pole n hh]
  split_ifs with hs
  · rw [cubicThetaShiftedPoleWeight hh,Complex.ofReal_mul,Complex.ofReal_ofNat]
    have he := cubicThetaCoefficientScalar (mul_ne_zero lambdaE_prime.ne_zero hh)
    have hi : -lambdaE*(lambdaE*h)=3*h := by
      rw [←mul_assoc,neg_mul,←pow_two,lambdaE_sq]
      ring
    rw [hi] at he
    rw [mul_assoc (3:ℂ) cubicThetaArithmeticBaseScalar,←he]
    unfold cubicThetaNormalizedObservedCoefficient cubicThetaObservedWhittakerCoefficient
    push_cast
    field_simp
    ring
  · simp only [mul_zero,zero_mul,zero_div]

end CubicFirstMoment

end

end OAI
