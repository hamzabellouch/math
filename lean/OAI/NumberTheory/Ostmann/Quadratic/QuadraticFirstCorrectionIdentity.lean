import OAI.NumberTheory.Ostmann.Quadratic.QuadraticGcdSecondTotal
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticSieveWeight

namespace OAI

/-! # The original first-transform correction is the finite signed gcd family -/

namespace Ostmann

open scoped Classical BigOperators ComplexConjugate

private theorem four_sum_rotate {ι κ ν μ : Type*}
    (S : Finset ι) (T : Finset κ) (U : Finset ν) (V : Finset μ) (F : ι → κ → ν → μ → ℂ) :
    (∑ z ∈ S, ∑ e ∈ T, ∑ a ∈ U, ∑ b ∈ V, F z e a b) =
      ∑ e ∈ T, ∑ a ∈ U, ∑ b ∈ V, ∑ z ∈ S, F z e a b := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  exact Finset.sum_comm

theorem quadratic_first_correction_identity (M R K D : ℕ) (H J : ℝ) (v w : ℕ → ℂ) :
    (∑ z ∈ quadraticGcdPairs (2 * R) D,
      v z.1 * conj (w z.2) * quadraticFirstSecondCorrections M D (quadraticPairKernel z.1 z.2) K H J) =
      ∑ e ∈ (2 * D).divisors, (ArithmeticFunction.moebius e : ℂ) *
        ∑ a : quadraticPoissonSigns,
          quadraticGcdSecondTotal quadraticSieveWeight (a : ℤ)
            (quadraticPoissonSigns_abs a.property) M H J R D e K ((e : ℤ) * a) v w := by
  unfold quadraticFirstSecondCorrections quadraticGcdSecondTotal quadraticGcdSecondFrequency
  simp only [Finset.mul_sum]
  rw [four_sum_rotate]
  apply Finset.sum_congr rfl
  intro e _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro z _
  simp only [jacobiSym.mul_left, Int.cast_mul]
  ring

end Ostmann

end OAI
