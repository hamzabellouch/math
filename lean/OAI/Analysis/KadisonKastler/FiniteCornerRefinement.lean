import OAI.Analysis.KadisonKastler.FiniteCornerGroups
import Mathlib.Logic.Equiv.Fintype

namespace OAI

/-! # Compatibility of finite signed corner groups -/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {n : ℕ}

/-- Extend a finite permutation by fixing the added last coordinate. -/
def cornerSuccessorPermutation (σ : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (n + 1)) :=
  σ.viaFintypeEmbedding ⟨Fin.castSucc, Fin.castSucc_injective n⟩

@[simp]
theorem cornerSuccessorPermutation_castSucc (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    cornerSuccessorPermutation σ i.castSucc = (σ i).castSucc :=
  Equiv.Perm.viaFintypeEmbedding_apply_image _ _ _

@[simp]
theorem cornerSuccessorPermutation_last (σ : Equiv.Perm (Fin n)) :
    cornerSuccessorPermutation σ (Fin.last n) = Fin.last n := by
  apply Equiv.Perm.viaFintypeEmbedding_apply_notMem_range
  rintro ⟨i, hi⟩
  exact Fin.castSucc_ne_last i hi

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {E : Submodule ℂ H} [CompleteSpace E]

namespace FullMatrixCorner

variable (F : FullMatrixCorner E)

theorem finiteSignedDiagonal_succ (d : Fin n → ℤˣ) :
    F.finiteSignedRepresentation (n + 1) (SemidirectProduct.inl (Fin.lastCases 1 d)) =
      F.finiteSignedRepresentation n (SemidirectProduct.inl d) := by
  apply Subtype.ext
  rw [F.finiteSignedRepresentation_diagonal, F.finiteSignedRepresentation_diagonal,
    Fin.sum_univ_castSucc]
  simp only [Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, Fin.val_last,
    Units.val_one, Int.cast_one, one_smul]
  simp only [partialDiagonal, Finset.sum_range_succ]
  abel

theorem finiteSignedPermutation_succ (σ : Equiv.Perm (Fin n)) :
    F.finiteSignedRepresentation (n + 1) (SemidirectProduct.inr (cornerSuccessorPermutation σ)) =
      F.finiteSignedRepresentation n (SemidirectProduct.inr σ) := by
  apply Subtype.ext
  rw [F.finiteSignedRepresentation_permutation, F.finiteSignedRepresentation_permutation,
    Fin.sum_univ_castSucc]
  simp only [cornerSuccessorPermutation_castSucc, cornerSuccessorPermutation_last,
    Fin.val_castSucc, Fin.val_last]
  simp only [partialDiagonal, Finset.sum_range_succ]
  abel

/-- These concrete finite subgroups increase with the finite corner. -/
theorem finiteSignedGroup_monotone : Monotone F.finiteSignedGroup := by
  apply monotone_nat_of_le_succ
  intro n u hu
  obtain ⟨g, rfl⟩ := hu
  refine ⟨SemidirectProduct.inl (Fin.lastCases 1 g.left) *
    SemidirectProduct.inr (cornerSuccessorPermutation g.right), ?_⟩
  rw [map_mul, F.finiteSignedDiagonal_succ, F.finiteSignedPermutation_succ,
    ← map_mul, SemidirectProduct.inl_left_mul_inr_right]

end FullMatrixCorner

end

end KadisonKastler

end OAI
