import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators Classical ComplexOrder MatrixOrder
open Matrix

namespace BinaryCoordinateSweeps.Density
variable {I J : Type*} [Fintype I] [DecidableEq I] [DecidableEq J]

lemma block_diagonal_commute (f : I → J) (Q : Matrix I I ℂ)
    (hQ : ∀ i j, f i ≠ f j → Q i j = 0) (a : J) :
    Commute Q (Matrix.diagonal (fun i => if f i = a then (1 : ℂ) else 0)) := by
  ext i j
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases h : f i = f j
  · rw [h]; ring
  · rw [hQ i j h]; ring

lemma sqrt_block_diagonal (f : I → J) (Q : Matrix I I ℂ)
    (hQ : ∀ i j, f i ≠ f j → Q i j = 0) :
    ∀ i j, f i ≠ f j → CFC.sqrt Q i j = 0 := by
  intro i j hij
  have h := (block_diagonal_commute f Q hQ (f i)).cfc_nnreal NNReal.sqrt
  rw [← CFC.sqrt_eq_cfc] at h
  have hh := congrFun (congrFun h.eq i) j
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, ite_true,
    ite_eq_right (Ne.symm hij), mul_zero, one_mul] at hh
  exact hh.symm

lemma sqrt_submatrix_invariant (Q : Matrix I I ℂ) (hQ : Q.PosSemidef)
    (e : Equiv.Perm I) (he : Q.submatrix e e = Q) :
    (CFC.sqrt Q).submatrix e e = CFC.sqrt Q := by
  apply Eq.symm
  apply CFC.sqrt_unique _ ((CFC.sqrt_nonneg Q).posSemidef.submatrix e).nonneg
  rw [Matrix.submatrix_mul_equiv, CFC.sqrt_mul_sqrt_self Q hQ.nonneg, he]

lemma sqrt_gram (Q : Matrix I I ℂ) (hQ : Q.PosSemidef) :
    CFC.sqrt Q * (CFC.sqrt Q).conjTranspose = Q := by
  rw [(CFC.sqrt_nonneg Q).posSemidef.1.eq, CFC.sqrt_mul_sqrt_self Q hQ.nonneg]

end BinaryCoordinateSweeps.Density

end

end OAI
