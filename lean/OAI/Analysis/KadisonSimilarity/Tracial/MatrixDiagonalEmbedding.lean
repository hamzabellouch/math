import OAI.Analysis.KadisonSimilarity.Tracial.MatrixSubfactorTransfer

namespace OAI

/-! The fixed diffuse matrix-generated factor is embedded diagonally in
its finite matrix amplifications. The normalized trace is unchanged. -/

noncomputable section
namespace KadisonSimilarity
open scoped ComplexOrder

variable {A : Type*} [CStarAlgebra A] (n : ℕ)

/-- The unital diagonal embedding into a finite C-star matrix algebra. -/
def matrixDiagonalHom : A →⋆ₐ[ℂ] CStarMatrix (Fin n) (Fin n) A :=
  CStarMatrix.ofMatrixStarAlgEquiv.toStarAlgHom.comp
    ({ Matrix.scalarAlgHom (Fin n) ℂ with
      map_star' := by
        intro a
        ext i j
        by_cases h : i = j
        · subst j
          simp [Matrix.scalar]
        · simp [Matrix.scalar, h, Ne.symm h] } :
      A →⋆ₐ[ℂ] Matrix (Fin n) (Fin n) A)

@[simp] theorem matrixDiagonalHom_apply (a : A) (i j : Fin n) :
    matrixDiagonalHom n a i j = if i = j then a else 0 := by
  change Matrix.diagonal (fun _ : Fin n => a) i j = _
  simp only [Matrix.diagonal_apply]

@[simp] theorem matrixDiagonalHom_diagonal (a : A) (i : Fin n) :
    matrixDiagonalHom n a i i = a := by simp

variable [NeZero n]

theorem matrixDiagonalHom_injective : Function.Injective (matrixDiagonalHom (A := A) n) := by
  intro a b h
  have := congrArg (fun X : CStarMatrix (Fin n) (Fin n) A => X 0 0) h
  simpa only [matrixDiagonalHom_diagonal] using this

variable [PartialOrder A] [StarOrderedRing A]

@[simp] theorem normalizedMatrixTrace_diagonal (τ : A →ₚ[ℂ] ℂ) (a : A) :
    normalizedMatrixTrace τ n (matrixDiagonalHom n a) = τ a := by
  rw [normalizedMatrixTrace_apply]
  simp only [matrixDiagonalHom_diagonal, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  exact mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr (NeZero.ne n))

variable {B : Type*} [CStarAlgebra B]

omit [NeZero n] [PartialOrder A] [StarOrderedRing A] in
/-- Diagonal inclusion and entrywise subfactor inclusion commute. -/
theorem matrixEntryHom_diagonal (φ : A →⋆ₐ[ℂ] B) (a : A) :
    matrixEntryHom φ (matrixDiagonalHom n a) = matrixDiagonalHom n (φ a) := by
  ext i j
  simp only [matrixEntryHom_apply, matrixDiagonalHom_apply]
  split_ifs <;> simp only [map_zero]

end KadisonSimilarity

end

end OAI
