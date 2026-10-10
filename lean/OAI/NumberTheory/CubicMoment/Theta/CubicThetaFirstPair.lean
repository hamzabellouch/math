import OAI.NumberTheory.CubicMoment.Estimates.CubicBesselFirstSlope
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaAxisDerivativeBalance
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimaryCoefficients
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaEven
import Mathlib.Analysis.Real.Pi.Bounds

namespace OAI

/-! The first two literal arithmetic Fourier terms have a uniformly
negative contribution at height one. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaFrequency_lambda : ‖cubicThetaFrequency lambdaE‖=Real.sqrt 3/9 := by
  simpa using cubicThetaFrequency_primary_norm (1:Eisenstein) 1

lemma cubicThetaArithmeticCoefficient_lambda : cubicThetaArithmeticCoefficient lambdaE=81 := by
  simpa [gauss_one] using cubicThetaArithmeticCoefficient_primary primary_one primary_one
    (squarefree_one : Squarefree (1:Eisenstein))

lemma cubicThetaFrequency_neg_norm (n : Eisenstein) :
    ‖cubicThetaFrequency (-n)‖=‖cubicThetaFrequency n‖ := by
  simp only [cubicThetaFrequency,Subalgebra.coe_neg,neg_div,norm_neg]

lemma cubicThetaFirstPair_real_bound :
    (cubicThetaSeriesTermVertical cubicThetaArithmeticCoefficient 0 1 lambdaE+
      cubicThetaSeriesTermVertical cubicThetaArithmeticCoefficient 0 1 (-lambdaE)).re≤ -5/2 := by
  let r := Real.sqrt 3/9
  have hr : 0<r := by dsimp [r]; positivity
  have hs : 173/100≤Real.sqrt 3 ∧ Real.sqrt 3≤7/4 := by
    constructor <;> nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤3),Real.sqrt_nonneg 3]
  have hx : 2≤4*Real.pi*r := by
    dsimp [r]
    have hp := Real.pi_gt_three
    nlinarith [Real.sqrt_nonneg 3]
  have hx' : 4*Real.pi*r≤5/2 := by
    dsimp [r]
    have hp := Real.pi_lt_d2
    nlinarith [Real.pi_pos]
  have hl := cubicWhittakerFirstSlope_lower hr hx hx'
  have hz : (-lambdaE:Eisenstein)≠0 := neg_ne_zero.mpr lambdaE_prime.ne_zero
  simp [cubicThetaSeriesTermVertical,lambdaE_prime.ne_zero,hz,
    cubicThetaArithmeticCoefficient_lambda,cubicThetaArithmeticCoefficient_even,
    cubicThetaFrequency_neg_norm,cubicThetaFrequency_lambda,tracePair,Complex.mul_re]
  change 81*(cubicThetaWhittakerDerivative r).re*r+
    81*(cubicThetaWhittakerDerivative r).re*r≤ -5/2
  have hr' : 173/900≤r := by dsimp [r]; linarith [hs.1]
  have hm := mul_le_mul_of_nonneg_right hl hr.le
  nlinarith

end CubicFirstMoment

end

end OAI
