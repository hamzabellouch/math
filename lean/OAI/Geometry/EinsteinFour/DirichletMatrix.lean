import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Tactic

namespace OAI

/-! Finite block matrices for the Jacobi determinant approximation. -/

namespace PositiveEinsteinFour.Jacobi

open Matrix OrderDual

noncomputable section

abbrev NormalMatrix := Matrix (Fin 3) (Fin 3) ℝ

/-- The normal-space matrix at one pair of mesh nodes. -/
def blockAt {N : ℕ} (M : Matrix (Fin 3 × Fin N) (Fin 3 × Fin N) ℝ)
    (i j : Fin N) : NormalMatrix := fun a b => M (a, i) (b, j)

theorem blockAt_mul {N : ℕ}
    (A B : Matrix (Fin 3 × Fin N) (Fin 3 × Fin N) ℝ) (i j : Fin N) :
    blockAt (A * B) i j = ∑ k, blockAt A i k * blockAt B k j := by
  ext a b
  simp only [blockAt, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.sum_apply]
  rw [Finset.sum_comm]

theorem blockAt_transpose {N : ℕ}
    (A : Matrix (Fin 3 × Fin N) (Fin 3 × Fin N) ℝ) (i j : Fin N) :
    blockAt A.transpose i j = (blockAt A j i).transpose := rfl

theorem blockAt_diagonal {N : ℕ} (S : Fin N → NormalMatrix) (i j : Fin N) :
    blockAt (Matrix.blockDiagonal S) i j = if i = j then S i else 0 := by
  ext a b
  by_cases h : i = j
  · subst j
    simp [blockAt]
  · simp [blockAt, Matrix.blockDiagonal_apply, h]

theorem blockAt_mul_diagonal {N : ℕ}
    (A : Matrix (Fin 3 × Fin N) (Fin 3 × Fin N) ℝ) (S : Fin N → NormalMatrix)
    (i j : Fin N) :
    blockAt (A * Matrix.blockDiagonal S) i j = blockAt A i j * S j := by
  rw [blockAt_mul]
  simp_rw [blockAt_diagonal, mul_ite, mul_zero]
  simp

theorem blockDiagonal_quadratic {N : ℕ} (S : Fin N → NormalMatrix)
    (x : Fin 3 × Fin N → ℝ) :
    star x ⬝ᵥ (Matrix.blockDiagonal S *ᵥ x) =
      ∑ i, star (fun a => x (a, i)) ⬝ᵥ (S i *ᵥ fun a => x (a, i)) := by
  simp only [star_trivial, dotProduct, Matrix.mulVec, Matrix.blockDiagonal_apply,
    Fintype.sum_prod_type]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [Finset.sum_comm]

/-- Positive pivots give a positive block-diagonal form. -/
theorem blockDiagonal_posDef {N : ℕ} {S : Fin N → NormalMatrix}
    (hS : ∀ i, (S i).PosDef) : (Matrix.blockDiagonal S).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · change (Matrix.blockDiagonal S).conjTranspose = Matrix.blockDiagonal S
    rw [Matrix.blockDiagonal_conjTranspose]
    congr 1
    funext i
    exact (hS i).isHermitian.eq
  · intro x hx
    rw [blockDiagonal_quadratic]
    have hn : ∃ i, (fun a => x (a, i)) ≠ 0 := by
      by_contra! hn
      apply hx
      funext p
      exact congrFun (hn p.2) p.1
    obtain ⟨i, hi⟩ := hn
    apply Finset.sum_pos'
    · intro j _
      exact (hS j).posSemidef.dotProduct_mulVec_nonneg _
    · exact ⟨i, Finset.mem_univ _, (hS i).dotProduct_mulVec_pos hi⟩

/-- A unit lower bidiagonal matrix, with arbitrary noncommuting blocks. -/
def lowerBidiagonal {N : ℕ} (A : Fin N → NormalMatrix) :
    Matrix (Fin 3 × Fin N) (Fin 3 × Fin N) ℝ := fun i j =>
  if i.2 = j.2 then (1 : NormalMatrix) i.1 j.1
  else if j.2.val + 1 = i.2.val then A j.2 i.1 j.1 else 0

private theorem lowerBidiagonal_triangular {N : ℕ} (A : Fin N → NormalMatrix) :
    (lowerBidiagonal A).BlockTriangular (fun i => toDual i.2) := by
  intro i j hij
  have hlt : i.2 < j.2 := hij
  have hne : i.2 ≠ j.2 := ne_of_lt hlt
  have hstep : ¬(j.2.val + 1 = i.2.val) := by omega
  simp [lowerBidiagonal, hne, hstep]

private def nodeBlockEquiv {N : ℕ} (i : (Fin N)ᵒᵈ) :
    {j : Fin 3 × Fin N // toDual j.2 = i} ≃ Fin 3 where
  toFun j := j.val.1
  invFun k := ⟨(k, ofDual i), rfl⟩
  left_inv j := by
    apply Subtype.ext
    exact Prod.ext rfl j.property.symm
  right_inv _ := rfl

private theorem lowerBidiagonal_block_det {N : ℕ} (A : Fin N → NormalMatrix)
    (i : (Fin N)ᵒᵈ) :
    ((lowerBidiagonal A).toSquareBlock (fun j => toDual j.2) i).det = 1 := by
  let e := nodeBlockEquiv i
  rw [← Matrix.det_reindex_self e]
  have heq : ((lowerBidiagonal A).toSquareBlock (fun j => toDual j.2) i).reindex
      e e = (1 : NormalMatrix) := by
    ext k l
    simp [Matrix.reindex_apply, Matrix.toSquareBlock, Matrix.toSquareBlockProp,
      lowerBidiagonal, e, nodeBlockEquiv]
  rw [heq, Matrix.det_one]

/-- The block formula used to recover the tridiagonal matrix from its
pivots. No products at different times have been interchanged. -/
theorem bidiagonal_factorization_block {N : ℕ} (A S : Fin N → NormalMatrix)
    (i j : Fin N) :
    blockAt (lowerBidiagonal A * Matrix.blockDiagonal S * (lowerBidiagonal A).transpose)
      i j = ∑ k, blockAt (lowerBidiagonal A) i k * S k *
        (blockAt (lowerBidiagonal A) j k).transpose := by
  rw [blockAt_mul]
  simp_rw [blockAt_mul_diagonal, blockAt_transpose]

/-- Elimination by these factors never changes a block determinant. -/
theorem det_lowerBidiagonal {N : ℕ} (A : Fin N → NormalMatrix) :
    (lowerBidiagonal A).det = 1 := by
  rw [(lowerBidiagonal_triangular A).det_fintype]
  simp only [lowerBidiagonal_block_det, Finset.prod_const_one]

/-- The determinant of an `L D Lᵀ` factorization is the product of the
three-dimensional pivots, with their original order retained. -/
theorem det_bidiagonal_factorization {N : ℕ} (A S : Fin N → NormalMatrix) :
    (lowerBidiagonal A * Matrix.blockDiagonal S * (lowerBidiagonal A).transpose).det =
      ∏ i, (S i).det := by
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    det_lowerBidiagonal, one_mul, mul_one, Matrix.det_blockDiagonal]

/-- Positive pivots give a positive discrete Jacobi form after the
unit triangular change of variables. -/
theorem bidiagonal_factorization_posDef {N : ℕ} (A S : Fin N → NormalMatrix)
    (hS : ∀ i, (S i).PosDef) :
    (lowerBidiagonal A * Matrix.blockDiagonal S * (lowerBidiagonal A).transpose).PosDef := by
  have hunit : IsUnit ((lowerBidiagonal A).transpose) := by
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    rw [Matrix.det_transpose, det_lowerBidiagonal]
    exact isUnit_one
  have h := (blockDiagonal_posDef hS).conjTranspose_mul_mul_same
    (Matrix.mulVec_injective_of_isUnit hunit)
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_transpose] using h

/-- The Jacobi recurrence is exactly the Schur-complement recurrence.
The order of the factors follows from right division by the Jacobi matrix. -/
theorem jacobi_pivot_recurrence {Yprev Y Ynext D : NormalMatrix}
    (hprev : IsUnit Yprev.det) (hY : IsUnit Y.det)
    (hrec : Ynext = D * Y - Yprev) :
    Ynext * Y⁻¹ = D - (Y * Yprev⁻¹)⁻¹ := by
  let : Invertible Yprev := ((Matrix.isUnit_iff_isUnit_det _).mpr hprev).invertible
  rw [hrec, Matrix.sub_mul, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hY,
    Matrix.mul_one, Matrix.mul_inv_rev, Matrix.inv_inv_of_invertible]

/-- The ordered Schur pivots telescope at the determinant level even when
successive Jacobi matrices do not commute. -/
theorem determinant_pivot_product (Y : ℕ → NormalMatrix) (n : ℕ)
    (hY : ∀ i ≤ n, (Y i).det ≠ 0) :
    (∏ i ∈ Finset.range n, (Y (i + 1) * (Y i)⁻¹).det) =
      (Y n).det / (Y 0).det := by
  induction n with
  | zero => simp [hY 0 le_rfl]
  | succ n ih =>
      rw [Finset.prod_range_succ, ih (fun i hi => hY i (Nat.le_succ_of_le hi)),
        Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
      field_simp [hY n (Nat.le_succ n), hY 0 (Nat.zero_le _)]

end

end PositiveEinsteinFour.Jacobi

end OAI
