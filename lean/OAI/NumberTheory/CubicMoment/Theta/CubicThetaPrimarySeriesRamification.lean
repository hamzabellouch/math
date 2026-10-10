import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimaryFourierTwist

namespace OAI

/-! The three primary twists are cycled by lambda in the frequency.
These are equalities of the actual primary series, before continuation. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicThetaPrimaryFourierSeries_period (e : Eisensteinˣ) (n : ℕ)
    (s : ℂ) (h : Eisenstein) :
    cubicThetaPrimaryFourierSeries e (n+3) s h=cubicThetaPrimaryFourierSeries e n s h := by
  unfold cubicThetaPrimaryFourierSeries
  apply tsum_congr
  intro a
  have hc := cubicSymbol_cube_of_isCoprime a.property lambdaE
    (primary_coprime_lambda a.property)
  unfold cubicThetaPrimaryFourierTerm
  rw [pow_add,hc,mul_one]

theorem cubicThetaPrimaryFourierSeries_lambda (e : Eisensteinˣ) (n : ℕ)
    (s : ℂ) (h : Eisenstein) :
    cubicThetaPrimaryFourierSeries e n s (lambdaE*h)=
      cubicThetaPrimaryFourierSeries e (n+1) s h := by
  unfold cubicThetaPrimaryFourierSeries
  apply tsum_congr
  intro a
  unfold cubicThetaPrimaryFourierTerm
  rw [mul_comm lambdaE h,cubicThetaSymbolFourier_mul a.property
    (primary_coprime_lambda a.property),← cubicSymbol_sq_eq_star a.property,
    pow_succ]
  ring

theorem cubicThetaPrimaryFourierSeries_lambda_pow (e : Eisensteinˣ) (n k : ℕ)
    (s : ℂ) (h : Eisenstein) :
    cubicThetaPrimaryFourierSeries e n s (lambdaE^k*h)=
      cubicThetaPrimaryFourierSeries e (n+k) s h := by
  induction k generalizing n with
  | zero => simp
  | succ k ih =>
    rw [pow_succ',mul_assoc,cubicThetaPrimaryFourierSeries_lambda,ih]
    congr 1
    omega

end CubicFirstMoment

end

end OAI
