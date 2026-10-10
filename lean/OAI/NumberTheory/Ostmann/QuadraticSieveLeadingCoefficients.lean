import OAI.NumberTheory.Ostmann.QuadraticSieveLeadingArithmetic

namespace OAI

namespace Ostmann.QuadraticSieve
open scoped ArithmeticFunction.Moebius

theorem dual_leading_coefficient (d q : ℕ) [NeZero q]
    (hd : Odd d) (hq : Odd q) (hsq : Squarefree q) :
    gaussSum (jacobiDirichletCharacter q) ZMod.stdAddChar *
      (∑ e ∈ (2 * d).divisors, ∑ a ∈ signedSquarefreeMultipliers,
        (μ e : ℂ) / (Real.sqrt (e : ℝ) : ℂ) * (jacobiSym ((e : ℤ) * a) q : ℂ) *
          (1 - (Real.sign (a : ℝ) : ℂ) * Complex.I) / (Real.sqrt |(a : ℝ)| : ℂ)) =
      (Real.sqrt (q : ℝ) : ℂ) * leadingDivisorCoefficient d q := by
  have hsum : (∑ e ∈ (2 * d).divisors, ∑ a ∈ signedSquarefreeMultipliers,
      (μ e : ℂ) / (Real.sqrt (e : ℝ) : ℂ) * (jacobiSym ((e : ℤ) * a) q : ℂ) *
        (1 - (Real.sign (a : ℝ) : ℂ) * Complex.I) / (Real.sqrt |(a : ℝ)| : ℂ)) =
      leadingDivisorCoefficient (2 * d) q * leadingSignCoefficient q := by
    unfold leadingDivisorCoefficient leadingSignCoefficient
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro e he
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    rw [jacobiSym.mul_left, Int.cast_mul]
    ring
  rw [hsum, leadingDivisorCoefficient_two_mul d q hd]
  calc
    _ = (gaussSum (jacobiDirichletCharacter q) ZMod.stdAddChar * leadingSignCoefficient q *
        (1 - (jacobiSym 2 q : ℂ) / (Real.sqrt 2 : ℂ))) * leadingDivisorCoefficient d q := by ring
    _ = _ := by rw [leadingSign_gauss_identity hq hsq]

theorem dual_leading_scale (e q M b : ℝ) (he : 0 < e) (hq : 0 < q) (hM : 0 < M) (hb : 0 < b) :
    M / (e * q) * Real.sqrt (e * q / (M * b)) =
      Real.sqrt (M / b) / (Real.sqrt e * Real.sqrt q) := by
  rw [Real.sqrt_div (by positivity), Real.sqrt_mul he.le,
    Real.sqrt_mul hM.le, Real.sqrt_div hM.le]
  have he0 := (Real.sqrt_pos.mpr he).ne'
  have hq0 := (Real.sqrt_pos.mpr hq).ne'
  have hM0 := (Real.sqrt_pos.mpr hM).ne'
  have hb0 := (Real.sqrt_pos.mpr hb).ne'
  field_simp
  ring_nf
  simp only [Real.sq_sqrt he.le, Real.sq_sqrt hq.le, Real.sq_sqrt hM.le]
  ring

end Ostmann.QuadraticSieve

end OAI
