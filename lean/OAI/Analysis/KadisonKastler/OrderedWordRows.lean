import OAI.Analysis.KadisonKastler.FockRelations
import OAI.Analysis.KadisonKastler.HilbertColumns
import OAI.Analysis.KadisonKastler.OrderedTuples

namespace OAI

/-! # Creation rows and annihilation columns indexed by ordered labels -/

namespace KadisonKastler

noncomputable section

variable {ι α H : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance orderedWordOrder : PartialOrder (H →L[ℂ] H) := CStarAlgebra.spectralOrder _
local instance orderedWordStarOrder : StarOrderedRing (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrderedRing _

namespace FreeDiagonalModel

variable (M : FreeDiagonalModel ι α H) (W : Finset α) {n : ℕ} (position : Fin n → ι)

def creationWord (t : OrderedLabelTuple W n) : H →L[ℂ] H :=
  tupleOperatorProduct (fun i => M.C (position i)) t.val

def annihilationWord (t : OrderedLabelTuple W n) : H →L[ℂ] H :=
  tupleOperatorProduct (fun i a => star (M.C (position i) a)) t.val

theorem norm_creationWord_row_le :
    ‖operatorRow (M.creationWord W position)‖ ≤ (Real.sqrt (Fintype.card α : ℝ))⁻¹ ^ n := by
  have hrest := norm_operatorRow_comp_le
    (tupleOperatorProduct (fun i => M.C (position i)))
    (Subtype.val : OrderedLabelTuple W n → (Fin n → α)) Subtype.val_injective
  exact hrest.trans (norm_tupleOperatorRow_le n _ (by positivity)
    (fun i => M.norm_creation_row_le (position i)))

theorem norm_annihilationWord_column_le :
    ‖operatorColumn (M.annihilationWord W position)‖ ≤
      (Real.sqrt (Fintype.card α : ℝ))⁻¹ ^ n := by
  have hrest := norm_operatorColumn_comp_le
    (tupleOperatorProduct (fun i a => star (M.C (position i) a)))
    (Subtype.val : OrderedLabelTuple W n → (Fin n → α)) Subtype.val_injective
  apply hrest.trans
  apply norm_tupleOperatorColumn_le n _ (by positivity)
  intro i
  rw [norm_operatorColumn_eq_row_star]
  simpa only [operatorRow, star_star] using M.norm_creation_row_le (position i)

theorem norm_creationWord_row_le_inv_sqrt :
    ‖operatorRow (M.creationWord W position)‖ ≤
      1 / Real.sqrt ((Fintype.card α : ℝ) ^ n) := by
  simpa only [inv_pow, ← sqrt_nat_pow (Nat.cast_nonneg (Fintype.card α)), one_div] using
    M.norm_creationWord_row_le W position

theorem norm_annihilationWord_column_le_inv_sqrt :
    ‖operatorColumn (M.annihilationWord W position)‖ ≤
      1 / Real.sqrt ((Fintype.card α : ℝ) ^ n) := by
  simpa only [inv_pow, ← sqrt_nat_pow (Nat.cast_nonneg (Fintype.card α)), one_div] using
    M.norm_annihilationWord_column_le W position

end FreeDiagonalModel

theorem norm_row_matrix_column_entry_le {I J : Type*} [Fintype I] [Fintype J]
    (L : I → H →L[ℂ] H) (T : CStarMatrix I J (H →L[ℂ] H)) (R : J → H →L[ℂ] H) :
    ‖(operatorRow L * T * operatorColumn R) () ()‖ ≤
      ‖operatorRow L‖ * ‖T‖ * ‖operatorColumn R‖ := by
  apply CStarMatrix.norm_entry_le_norm.trans
  exact (rectangularOperator_norm_mul_le _ _).trans
    (mul_le_mul_of_nonneg_right (rectangularOperator_norm_mul_le _ _) (norm_nonneg _))

end

end KadisonKastler

end OAI
