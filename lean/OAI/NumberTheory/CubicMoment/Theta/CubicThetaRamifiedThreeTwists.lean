import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRamifiedPrimaryContinuation

namespace OAI

/-! All three primary lambda twists inherit actual holomorphic
pole-cleared continuations by cycling the nonzero frequency. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaRegularizedPrimaryTwist (j : Fin 3) (h : Eisenstein) (s : ℂ) : ℂ :=
  cubicThetaRegularizedPrimaryOne (lambdaE^(((j:ℕ)+2)%3)*h) s

theorem cubicThetaRegularizedPrimaryTwist_analytic (j : Fin 3)
    {h : Eisenstein} (hh : h≠0) :
    AnalyticOnNhd ℂ (cubicThetaRegularizedPrimaryTwist j h) {s : ℂ | 1<s.re} :=
  cubicThetaRegularizedPrimaryOne_analytic
    (mul_ne_zero (pow_ne_zero _ lambdaE_prime.ne_zero) hh)

theorem cubicThetaRegularizedPrimaryTwist_right (j : Fin 3)
    {h : Eisenstein} (hh : h≠0) {s : ℂ} (hs : 3<s.re) :
    cubicThetaRegularizedPrimaryTwist j h s=
      (s-4/3)*cubicThetaPrimaryFourierSeries 1 (j:ℕ) s h := by
  unfold cubicThetaRegularizedPrimaryTwist
  rw [cubicThetaRegularizedPrimaryOne_right
    (mul_ne_zero (pow_ne_zero _ lambdaE_prime.ne_zero) hh) hs,
    cubicThetaPrimaryFourierSeries_lambda_pow]
  congr 1
  fin_cases j
  · simpa only [Nat.reduceAdd,Nat.reduceMod] using
      cubicThetaPrimaryFourierSeries_period 1 0 s h
  · rfl
  · rfl

end CubicFirstMoment

end

end OAI
