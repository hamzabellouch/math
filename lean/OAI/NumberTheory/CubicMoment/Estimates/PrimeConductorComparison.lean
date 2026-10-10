import OAI.NumberTheory.CubicMoment.Estimates.PrimaryPrimeEstimateTransfer
import OAI.NumberTheory.CubicMoment.Estimates.KummerPrimeFromPrimitive

namespace OAI

/-! The polynomial conductor cost of a finite Euler correction preserves
the explicit exponential prime error after a fixed change of constants. -/
noncomputable section
namespace CubicFirstMoment

lemma primeCancellation_polynomial_conductor {c Q X : ℝ} (hc : 0 ≤ c)
    (hQ : 1 ≤ Q) (hXp : 0 < X) (hL : 1 ≤ Real.log X) :
    primeCancellationWeight c (4*Q^2) X ≤ 25*heckeExponentialError (c/5) X Q := by
  have hQp : 0 < Q := by linarith
  have hR : 1 ≤ 4*Q^2 := by nlinarith
  have hlogQ : 0 ≤ Real.log Q := Real.log_nonneg hQ
  have hlog4 : Real.log (4:ℝ) ≤ 3 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4)
    linarith
  have hlogR : Real.log (4*Q^2) = Real.log 4+2*Real.log Q := by
    rw [Real.log_mul (by norm_num) (pow_ne_zero 2 hQp.ne'),Real.log_pow]
    norm_num
  have hd := primeContourDenominator_ge_one hQ hL
  have hdR := primeContourDenominator_ge_one hR hL
  have hden : primeContourDenominator (4*Q^2) X ≤ 5*primeContourDenominator Q X := by
    unfold primeContourDenominator at *
    rw [hlogR]
    nlinarith [Real.sqrt_nonneg (Real.log X)]
  have hratio : Real.log X/(5*primeContourDenominator Q X) ≤
      Real.log X/primeContourDenominator (4*Q^2) X :=
    div_le_div_of_nonneg_left (by linarith) (by linarith) hden
  have he : Real.exp (-c*Real.log X/primeContourDenominator (4*Q^2) X) ≤
      Real.exp (-(c/5)*Real.log X/primeContourDenominator Q X) := by
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left hratio hc
    convert neg_le_neg hh using 1 <;> ring
  have hP := (primeLogSize_bounds hQ hXp hL).1
  have hPR := (primeLogSize_bounds hR hXp hL).1
  have hlogs : Real.log (X*(4*Q^2)) ≤ 5*Real.log (X*Q) := by
    rw [Real.log_mul hXp.ne' (by positivity),hlogR,Real.log_mul hXp.ne' hQp.ne']
    nlinarith
  have hp2 : (Real.log (X*(4*Q^2)))^2 ≤ 25*(Real.log (X*Q))^4 := by
    have hh := pow_le_pow_left₀ (by linarith : 0 ≤ Real.log (X*(4*Q^2))) hlogs 2
    have hp : (Real.log (X*Q))^2 ≤ (Real.log (X*Q))^4 := by
      nlinarith [sq_nonneg ((Real.log (X*Q))^2-1)]
    nlinarith only [hh,hp]
  unfold primeCancellationWeight heckeExponentialError primeContourDenominator at *
  have hh := mul_le_mul (mul_le_mul_of_nonneg_left hp2 hXp.le) he (Real.exp_pos _).le (by positivity)
  nlinarith only [hh]

end CubicFirstMoment

end

end OAI
