import OAI.GroupTheory.PolycyclicRecognition.Algebra.FiniteWordBases
import OAI.GroupTheory.PolycyclicRecognition.Geometry.WeightedColumnBasis
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

namespace OAI

/-! # Maximizing actual word bases

Invertible selections from the coordinate matrix are exactly the actual word
bases. Thus the finite maximizing-basis argument applies to the Lie word list.
-/

noncomputable section

namespace PolycyclicRecognition

open Module

variable {I L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  (X : I → L) (S : Finset (FreeMagma I))
  (b₀ : Basis (Fin (finrank ℝ L)) ℝ L)

def wordListCoordinates (w : S) : Fin (finrank ℝ L) → ℝ := b₀.equivFun (evalBracketWord X w)

omit [FiniteDimensional ℝ L] in
theorem wordBasis_det_ne_zero (β : WordBasisSelections X S) :
    (columnBasisMatrix (wordListCoordinates X S b₀) β.val).det ≠ 0 := by
  let b := WordBasisSelections.basis X S β
  have he : columnBasisMatrix (wordListCoordinates X S b₀) β.val = b₀.toMatrix b := by
    ext i j
    change b₀.repr (evalBracketWord X (β.val j)) i = b₀.repr (b j) i
    exact congrArg (fun v : L => b₀.repr v i) (WordBasisSelections.eval_words X S β j)
  rw [he]
  let := b₀.invertibleToMatrix b
  exact isUnit_iff_ne_zero.mp (Matrix.isUnit_det_of_invertible _)

omit [FiniteDimensional ℝ L] in
/-- The matrix coordinates agree with the intrinsic coordinates in the
selected word basis. -/
theorem columnCoordinates_eq_wordBasis_repr (β : WordBasisSelections X S) (y : S) :
    columnCoordinates (wordListCoordinates X S b₀) β.val y =
      (WordBasisSelections.basis X S β).equivFun (evalBracketWord X y) := by
  let b := WordBasisSelections.basis X S β
  have he : columnBasisMatrix (wordListCoordinates X S b₀) β.val = b₀.toMatrix b := by
    ext i j
    exact congrArg (fun v : L => b₀.repr v i) (WordBasisSelections.eval_words X S β j)
  have hi : (b₀.toMatrix b)⁻¹ = b.toMatrix b₀ :=
    Matrix.inv_eq_left_inv (b.toMatrix_mul_toMatrix_flip b₀)
  unfold columnCoordinates
  rw [he, hi]
  exact b₀.toMatrix_mulVec_repr b (evalBracketWord X y)

/-- An invertible coordinate selection gives precisely the actual word basis
needed for the finite family, including dimension zero. -/
def wordBasisOfDet (w : Fin (finrank ℝ L) → S)
    (hw : (columnBasisMatrix (wordListCoordinates X S b₀) w).det ≠ 0) :
    WordBasisSelections X S := by
  have hli : LinearIndependent ℝ (fun j => evalBracketWord X (w j)) := by
    apply LinearIndependent.of_comp b₀.equivFun.toLinearMap
    exact Matrix.linearIndependent_cols_of_det_ne_zero hw
  let b := basisOfLinearIndependentOfCardEqFinrank'
    (fun j => evalBracketWord X (w j)) hli (Fintype.card_fin _)
  exact ⟨w, b, fun j => (congrFun (coe_basisOfLinearIndependentOfCardEqFinrank'
    (fun j => evalBracketWord X (w j)) hli (Fintype.card_fin _)) j).symm⟩

@[simp] theorem wordBasisOfDet_val (w : Fin (finrank ℝ L) → S)
    (hw : (columnBasisMatrix (wordListCoordinates X S b₀) w).det ≠ 0) :
    (wordBasisOfDet X S b₀ w hw).val = w := rfl

/-- Maximizing over actual bases also maximizes over every invertible column
selection. This connects the intrinsic list to the box coordinate estimates. -/
theorem exists_maximizing_wordBasis [Nonempty (WordBasisSelections X S)]
    (cost : S → ℝ) : ∃ β : WordBasisSelections X S,
      IsMaximizingColumnBasis (wordListCoordinates X S b₀) cost β.val := by
  classical
  obtain ⟨β, _, hβ⟩ := Finset.exists_max_image Finset.univ
    (fun β : WordBasisSelections X S => columnBasisWeight cost β.val) Finset.univ_nonempty
  refine ⟨β, wordBasis_det_ne_zero X S b₀ β, ?_⟩
  intro w hw
  simpa only [wordBasisOfDet_val] using
    hβ (wordBasisOfDet X S b₀ w hw) (Finset.mem_univ _)

end PolycyclicRecognition

end

end OAI
