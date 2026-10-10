import Mathlib.Tactic

namespace OAI

/-!
# The high angular degree polynomial certificate

Exact rational comparisons from Appendix `cert:high-angular` of
*Stable self-similar blowup for a supercritical defocusing Schrödinger equation
on the torus* (September 2026) give positivity of the multiplier polynomial.
-/

namespace DefocusingNLS

/-- The rational lower bound in equation `free:high-polynomial`. -/
noncomputable def highAngularPolynomial (t : ℝ) : ℝ :=
  let u₀ := 99 / 1000 + 98 / 100 * t
  let L₀ := 113 / 100 + 98 / 100 * t
  let d₀ := (1 / 10 + 981 / 1000 * t) ^ 2 + (272 / 100 + 1 / 5 * t) ^ 2
  let q₀ := 1 + 3 / 2 * t
  (-3 - 1 / 32 + u₀ / 4) * L₀ * d₀ * q₀ ^ 2 +
    (81 / 4) * u₀ * L₀ * q₀ ^ 2 + 5 * L₀ * d₀ -
    (-3 / 2 + 11 / 4 * t) ^ 2 * d₀

/-- The comparison polynomial in Appendix `cert:high-angular`. -/
noncomputable def highAngularComparison (t : ℝ) : ℝ :=
  2 + t * (33 - 361 / 5 * t + 224 / 5 * t ^ 2) +
    t ^ 4 * (179 / 10 - 461 / 100 * t + 27 / 50 * t ^ 2)

/-- All seven coefficients of the difference, checked as a polynomial identity. -/
theorem highAngular_difference (t : ℝ) :
    highAngularPolynomial t - highAngularComparison t =
      142518401 / 500000000 + 325932989 / 1000000000 * t +
      15777215591 / 200000000000 * t ^ 2 +
      8728703679 / 200000000000 * t ^ 3 +
      34209914771 / 800000000000 * t ^ 4 +
      16113799 / 3125000000 * t ^ 5 +
      60018849 / 40000000000 * t ^ 6 := by
  unfold highAngularPolynomial highAngularComparison
  ring

/-- The first quadratic is strictly positive, by completing the square. -/
theorem highAngular_first_quadratic_pos (t : ℝ) :
    0 < 33 - 361 / 5 * t + 224 / 5 * t ^ 2 := by
  nlinarith [sq_nonneg (448 * t - 361)]

/-- The second quadratic is strictly positive, by completing the square. -/
theorem highAngular_second_quadratic_pos (t : ℝ) :
    0 < 179 / 10 - 461 / 100 * t + 27 / 50 * t ^ 2 := by
  nlinarith [sq_nonneg (108 * t - 461)]

/-- The comparison polynomial is at least two on the positive half-line. -/
theorem highAngularComparison_ge_two {t : ℝ} (ht : 0 ≤ t) :
    2 ≤ highAngularComparison t := by
  have h₁ := mul_nonneg ht (highAngular_first_quadratic_pos t).le
  have h₂ := mul_nonneg (pow_nonneg ht 4) (highAngular_second_quadratic_pos t).le
  unfold highAngularComparison
  linarith

/-- The manuscript's exact polynomial lower bound is strictly positive. -/
theorem highAngularPolynomial_pos {t : ℝ} (ht : 0 ≤ t) :
    0 < highAngularPolynomial t := by
  have hdiff : 0 < highAngularPolynomial t - highAngularComparison t := by
    rw [highAngular_difference]
    positivity
  have hcomp := highAngularComparison_ge_two ht
  linarith

end DefocusingNLS

end OAI
