import OAI.NumberTheory.Ostmann.Quadratic.QuadraticFresnelSigns

namespace OAI

/-! # Exact arithmetic identification of the first Poisson main coefficient -/

namespace Ostmann

open scoped Classical BigOperators

theorem quadratic_fresnel_scaled_sign_sum (q e : ℕ) :
    (∑ a ∈ ({1, -1, 2, -2} : Finset ℤ),
      (jacobiSym ((e : ℤ) * a) q : ℂ) * quadraticFresnelPhase a /
        (Real.sqrt |(a : ℝ)| : ℂ)) =
      (jacobiSym (e : ℤ) q : ℂ) * quadraticFresnelSignSum q := by
  unfold quadraticFresnelSignSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [jacobiSym.mul_left, Int.cast_mul]
  ring

theorem quadratic_fresnel_arithmetic {q D : ℕ}
    (hq : Squarefree q) (ho : Odd q) (hD : Odd D) :
    quadraticGaussMultiplier q *
      (∑ e ∈ (2 * D).divisors,
        ((ArithmeticFunction.moebius e : ℂ) / (Real.sqrt (e : ℝ) : ℂ)) *
          ∑ a ∈ ({1, -1, 2, -2} : Finset ℤ),
            (jacobiSym ((e : ℤ) * a) q : ℂ) * quadraticFresnelPhase a /
              (Real.sqrt |(a : ℝ)| : ℂ)) =
      ∑ d ∈ D.divisors, (ArithmeticFunction.moebius d : ℂ) *
        quadraticRootCharacter q d := by
  simp_rw [quadratic_fresnel_scaled_sign_sum]
  calc
    _ = quadraticGaussMultiplier q *
        ((∑ e ∈ (2 * D).divisors, (ArithmeticFunction.moebius e : ℂ) *
          quadraticRootCharacter q e) * quadraticFresnelSignSum q) := by
      congr 1
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro e _
      unfold quadraticRootCharacter
      ring
    _ = (quadraticGaussMultiplier q * quadraticFresnelSignSum q) *
        (1 - quadraticRootCharacter q 2) *
        (∑ d ∈ D.divisors, (ArithmeticFunction.moebius d : ℂ) *
          quadraticRootCharacter q d) := by
      rw [quadratic_root_euler_two q D hD]
      ring
    _ = (2 - 2 * quadraticRootCharacter q 2 ^ 2) *
        (∑ d ∈ D.divisors, (ArithmeticFunction.moebius d : ℂ) *
          quadraticRootCharacter q d) := by
      rw [quadratic_fresnel_sign_sum hq ho]
      ring
    _ = _ := by rw [quadratic_root_two_square ho]; ring

end Ostmann

end OAI
