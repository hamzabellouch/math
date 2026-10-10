import Mathlib.Algebra.Polynomial.Degree.TrailingDegree
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Basic.Complex.Basic

namespace OAI

namespace InvariantProjection

open Polynomial

theorem exists_nonzero_product_coeff_le
    {R : Type*} [Semiring R] [NoZeroDivisors R]
    (A B : R[X]) (k l : ℕ)
    (hA : A.coeff k ≠ 0) (hB : B.coeff l ≠ 0) :
    ∃ n ≤ k + l, (A * B).coeff n ≠ 0 := by
  have hA0 : A ≠ 0 := by
    intro h
    simp [h] at hA
  have hB0 : B ≠ 0 := by
    intro h
    simp [h] at hB
  refine ⟨(A * B).natTrailingDegree, ?_, ?_⟩
  · rw [natTrailingDegree_mul hA0 hB0]
    exact Nat.add_le_add
      (natTrailingDegree_le_of_ne_zero hA)
      (natTrailingDegree_le_of_ne_zero hB)
  · exact coeff_natTrailingDegree_ne_zero.mpr (mul_ne_zero hA0 hB0)

theorem exists_nonzero_product_coeff_le_two_mul
    (A B : ℂ[X]) (K : ℕ)
    (hA : A.coeff K ≠ 0) (hB : B.coeff K ≠ 0) :
    ∃ n ≤ 2 * K, (A * B).coeff n ≠ 0 := by
  simpa [two_mul] using exists_nonzero_product_coeff_le A B K K hA hB

end InvariantProjection

end OAI
