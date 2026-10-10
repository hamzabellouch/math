import Mathlib

namespace OAI

/-! Finite matrix expansions for the two trace moments in the IMM argument.
These identities contain no analytic or asymptotic assumptions. -/

noncomputable section
open scoped BigOperators Matrix

namespace Problem335

variable {I J P R : Type*} [Fintype I] [Fintype J] [Fintype P]
  [DecidableEq I] [DecidableEq J]

/-- A matrix whose column is a weighted sum of path shifts. -/
def pathShiftMatrix [AddCommMonoid R] (shift : I → P → J) (weight : I → P → R) :
    Matrix J I R := by
  classical
  exact fun j i => ∑ p, if shift i p = j then weight i p else 0

/-- Expanding a real Gram matrix gives the sum of squared entries. -/
theorem trace_transpose_mul_self {I : Type u_1} {J : Type u_2}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] (A : Matrix J I ℝ) :
    Matrix.trace (A.transpose * A) = ∑ i, ∑ j, (A j i) ^ 2 := by
  simp [Matrix.trace, Matrix.mul_apply, pow_two]

/-- The second moment is the sum of squares of all Gram entries. -/
theorem trace_gram_sq {I : Type u_1} {J : Type u_2}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] (A : Matrix J I ℝ) :
    Matrix.trace ((A.transpose * A) ^ 2) =
      ∑ i, ∑ k, (∑ j, A j i * A j k) ^ 2 := by
  simp only [pow_two, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.transpose_apply]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro k hk
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- The Gram entry is a weighted count of pairs of paths with equal shifts. -/
theorem pathShiftMatrix_gram_apply
    {I : Type u_1} {J : Type u_2} {P : Type u_3} {R : Type u_4}
    [Fintype I] [Fintype J] [Fintype P] [DecidableEq I] [DecidableEq J] [CommSemiring R]
    (shift : I → P → J) (weight : I → P → R) (i k : I) :
    ((pathShiftMatrix shift weight).transpose * pathShiftMatrix shift weight) i k =
      ∑ p, ∑ q, if shift i p = shift k q then weight i p * weight k q else 0 := by
  classical
  simp only [Matrix.mul_apply, Matrix.transpose_apply, pathShiftMatrix]
  simp_rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q hq
  simp only [ite_mul, zero_mul, mul_ite, mul_zero]
  simp [eq_comm]

/-- It is enough that distinct paths reaching the same row have zero weight product.
This permits invalid path shifts to be given arbitrary target indices when their
weight is zero. -/
theorem pathShiftMatrix_first_trace [CommSemiring R]
    (shift : I → P → J) (weight : I → P → R)
    (hdisjoint : ∀ i p q, p ≠ q → shift i p = shift i q →
      weight i p * weight i q = 0) :
    Matrix.trace ((pathShiftMatrix shift weight).transpose * pathShiftMatrix shift weight) =
      ∑ i, ∑ p, weight i p ^ 2 := by
  classical
  simp only [Matrix.trace, Matrix.diag_apply, pathShiftMatrix_gram_apply]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.sum_eq_single p]
  · simp [pow_two]
  · intro q hq hqp
    by_cases hs : shift i p = shift i q
    · simp [hs, hdisjoint i p q (Ne.symm hqp) hs]
    · simp [hs]
  · simp

/-- Columnwise injectivity of the path shifts implies the first trace identity. -/
theorem pathShiftMatrix_first_trace_of_injective [CommSemiring R]
    (shift : I → P → J) (weight : I → P → R)
    (hinj : ∀ i, Function.Injective (shift i)) :
    Matrix.trace ((pathShiftMatrix shift weight).transpose * pathShiftMatrix shift weight) =
      ∑ i, ∑ p, weight i p ^ 2 := by
  apply pathShiftMatrix_first_trace
  intro i p q hpq hshift
  exact (hpq (hinj i hshift)).elim

/-- The second trace is the squared-overlap sum of the weighted path shifts. -/
theorem pathShiftMatrix_second_trace
    (shift : I → P → J) (weight : I → P → ℝ) :
    Matrix.trace (((pathShiftMatrix shift weight).transpose *
      pathShiftMatrix shift weight) ^ 2) =
      ∑ i, ∑ k, (∑ p, ∑ q,
        if shift i p = shift k q then weight i p * weight k q else 0) ^ 2 := by
  rw [trace_gram_sq]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro k hk
  congr 1
  exact pathShiftMatrix_gram_apply shift weight i k

/-- Frobenius expansion over the complex numbers, with the genuine adjoint. -/
theorem trace_conjTranspose_mul_self_complex {I : Type u_1} {J : Type u_2}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] (A : Matrix J I ℂ) :
    Matrix.trace (A.conjTranspose * A) =
      ∑ i, ∑ j, (Complex.normSq (A j i) : ℂ) := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Complex.normSq_eq_conj_mul_self]
  rfl

/-- The complete four-path expansion of the second trace moment. -/
theorem pathShiftMatrix_second_trace_four_paths
    (shift : I → P → J) (weight : I → P → ℝ) :
    Matrix.trace (((pathShiftMatrix shift weight).transpose *
      pathShiftMatrix shift weight) ^ 2) =
      ∑ i, ∑ k, ∑ p, ∑ q, ∑ r, ∑ s,
        if shift i p = shift k q ∧ shift i r = shift k s then
          weight i p * weight k q * weight i r * weight k s else 0 := by
  rw [pathShiftMatrix_second_trace]
  simp only [pow_two]
  simp_rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro s hs
  by_cases h₁ : shift i p = shift k q <;>
    by_cases h₂ : shift i r = shift k s <;> simp [h₁, h₂, mul_assoc]

/-- Square-root path weights yield the sum of the underlying occupation masses.
Zero-mass invalid paths need not have distinct shifts. -/
theorem pathShiftMatrix_first_trace_sqrt
    (shift : I → P → J) (mass : I → P → ℝ)
    (hnonneg : ∀ i p, 0 ≤ mass i p)
    (hdisjoint : ∀ i p q, p ≠ q → shift i p = shift i q →
      mass i p = 0 ∨ mass i q = 0) :
    Matrix.trace ((pathShiftMatrix shift (fun i p => Real.sqrt (mass i p))).transpose *
      pathShiftMatrix shift (fun i p => Real.sqrt (mass i p))) =
      ∑ i, ∑ p, mass i p := by
  rw [pathShiftMatrix_first_trace]
  · simp [Real.sq_sqrt, hnonneg]
  · intro i p q hpq hshift
    rcases hdisjoint i p q hpq hshift with h | h <;> simp [h]

end Problem335

end

end OAI
