import OAI.Analysis.KadisonKastler.FaithfulRepresentation
import Mathlib.Tactic.FinCases

namespace OAI

/-!
# Two-by-two C⋆-matrix norm formulas

The diagonal embedding is a faithful star representation, so its norm is
the supremum norm. Multiplying by the flip unitary gives the corresponding
off-diagonal formula.
-/

namespace KadisonKastler

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The diagonal star representation of a finite product of C⋆-algebras. -/
def diagonalStarAlgHom (n : Type*) [Fintype n] [DecidableEq n] :
    (n → A) →⋆ₐ[ℂ] CStarMatrix n n A :=
  { Matrix.diagonalAlgHom ℂ with
    map_star' d := by
      ext i j
      change (if i = j then star (d i) else 0) =
        star (if j = i then d j else 0)
      by_cases hij : i = j
      · subst j
        simp
      · simp [hij, Ne.symm hij] }

omit [PartialOrder A] [StarOrderedRing A] in
@[simp]
theorem diagonalStarAlgHom_apply (n : Type*) [Fintype n] [DecidableEq n]
    (d : n → A) (i j : n) :
    diagonalStarAlgHom n d i j = if i = j then d i else 0 := rfl

omit [PartialOrder A] [StarOrderedRing A] in
theorem diagonalStarAlgHom_injective (n : Type*) [Fintype n] [DecidableEq n] :
    Function.Injective (diagonalStarAlgHom (A := A) n) := by
  intro d e h
  funext i
  have hi := congrArg (fun M : CStarMatrix n n A => M i i) h
  simpa only [diagonalStarAlgHom_apply, ↓reduceIte] using hi

/-- The operator norm of a diagonal matrix is the finite-product norm. -/
theorem norm_diagonalStarAlgHom (n : Type*) [Fintype n] [DecidableEq n] (d : n → A) :
    ‖diagonalStarAlgHom n d‖ = ‖d‖ :=
  injective_starAlgHom_norm _ (diagonalStarAlgHom_injective n) d

/-- The diagonal matrix with entries `a` and `b`. -/
def blockDiagonal (a b : A) : CStarMatrix (Fin 2) (Fin 2) A :=
  diagonalStarAlgHom (Fin 2) ![a, b]

theorem norm_blockDiagonal (a b : A) : ‖blockDiagonal a b‖ = max ‖a‖ ‖b‖ := by
  rw [blockDiagonal, norm_diagonalStarAlgHom]
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (le_trans (norm_nonneg a) (le_max_left _ _))).mpr
    intro i
    fin_cases i <;> simp
  · exact max_le (norm_le_pi_norm ![a, b] 0) (norm_le_pi_norm ![a, b] 1)

/-- The unitary that swaps the two coordinates. -/
def blockFlip : unitary (CStarMatrix (Fin 2) (Fin 2) A) :=
  let S : CStarMatrix (Fin 2) (Fin 2) A := fun i j => if i = j then 0 else 1
  ⟨S, by
    change star S * S = 1 ∧ S * star S = 1
    constructor <;> ext i j
    all_goals
      simp only [CStarMatrix.mul_apply, CStarMatrix.star_apply, Fin.sum_univ_two]
      fin_cases i <;> fin_cases j <;> simp [S]⟩

/-- The off-diagonal matrix with entries `a` and `b`. -/
def blockOffDiagonal (a b : A) : CStarMatrix (Fin 2) (Fin 2) A :=
  !![0, a; b, 0]

omit [PartialOrder A] [StarOrderedRing A] in
theorem blockOffDiagonal_eq_mul_flip (a b : A) :
    blockOffDiagonal a b =
      blockDiagonal a b * (blockFlip (A := A) : CStarMatrix (Fin 2) (Fin 2) A) := by
  ext i j
  simp only [CStarMatrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;>
    simp [blockOffDiagonal, blockDiagonal, blockFlip]

theorem norm_blockOffDiagonal (a b : A) : ‖blockOffDiagonal a b‖ = max ‖a‖ ‖b‖ := by
  rw [blockOffDiagonal_eq_mul_flip, CStarRing.norm_mul_coe_unitary, norm_blockDiagonal]

omit [PartialOrder A] [StarOrderedRing A] in
/-- The lower-left entry of an operator commuting with a diagonal pair
is an intertwiner for that pair. -/
theorem block_commute_intertwines (D : CStarMatrix (Fin 2) (Fin 2) A) (a b : A)
    (h : D * blockDiagonal a b = blockDiagonal a b * D) :
    D 1 0 * a = b * D 1 0 := by
  have he := congrArg (fun M : CStarMatrix (Fin 2) (Fin 2) A => M 1 0) h
  simp only [CStarMatrix.mul_apply, Fin.sum_univ_two] at he
  change D 1 0 * a + D 1 1 * 0 = 0 * D 0 0 + b * D 1 0 at he
  simpa using he

/-- Closeness to the flip controls the lower-left intertwiner. -/
theorem norm_lowerLeft_sub_one_le (D : CStarMatrix (Fin 2) (Fin 2) A) :
    ‖D 1 0 - 1‖ ≤ ‖D - (blockFlip (A := A) : CStarMatrix (Fin 2) (Fin 2) A)‖ := by
  have h := CStarMatrix.norm_entry_le_norm
    (M := D - (blockFlip (A := A) : CStarMatrix (Fin 2) (Fin 2) A)) (i := 1) (j := 0)
  simp only [CStarMatrix.sub_apply] at h
  simpa [blockFlip] using h

/-- Every individual entry is bounded by the operator norm, at any size. -/
theorem matrix_entry_norm_le {m n : Type*} [Fintype m] [Fintype n]
    (M : CStarMatrix m n A) (i : m) (j : n) : ‖M i j‖ ≤ ‖M‖ :=
  CStarMatrix.norm_entry_le_norm

end

end KadisonKastler

end OAI
