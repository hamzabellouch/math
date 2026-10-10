import OAI.Analysis.KadisonKastler.OrderedWordRows
import OAI.Analysis.KadisonKastler.CutFactorization

namespace OAI

/-! # Norm estimates for actual cuts in the free diagonal model -/

namespace KadisonKastler.FreeDiagonalModel

open Finset

noncomputable section

variable {ι α H : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance freeCutOrder : PartialOrder (H →L[ℂ] H) := CStarAlgebra.spectralOrder _
local instance freeCutStarOrder : StarOrderedRing (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrderedRing _

variable (M : FreeDiagonalModel ι α H) (W : Finset α) {p q : ℕ}

theorem norm_noPreservationSum_le (hW : W.card = p + q)
    (left : Fin p → ι) (right : Fin q → ι) :
    ‖∑ t : OrderedLabelTuple W (p + q),
      M.creationWord W left (tupleInitial t) * M.annihilationWord W right (tupleFinal t)‖ ≤
      Real.sqrt ((p + q).factorial : ℝ) /
        Real.sqrt ((Fintype.card α : ℝ) ^ (p + q)) := by
  rw [noPreservation_sum_eq_sandwich]
  apply (norm_row_matrix_column_entry_le _ _ _).trans
  have hT := norm_orderedNoPreservationMatrix_le_sqrt_factorial (H := H) W q p (by omega)
  have hT' : ‖orderedNoPreservationMatrix (H := H) W q p‖ ≤
      Real.sqrt ((p + q).factorial : ℝ) := by simpa only [Nat.add_comm q p] using hT
  calc
    _ ≤ ((Real.sqrt (Fintype.card α : ℝ))⁻¹ ^ p) *
        Real.sqrt ((p + q).factorial : ℝ) * ((Real.sqrt (Fintype.card α : ℝ))⁻¹ ^ q) := by
      apply mul_le_mul
      · exact mul_le_mul (M.norm_creationWord_row_le W left) hT' (norm_nonneg _) (by positivity)
      · exact M.norm_annihilationWord_column_le W right
      · positivity
      · positivity
    _ = Real.sqrt ((p + q).factorial : ℝ) *
        ((Real.sqrt (Fintype.card α : ℝ))⁻¹ ^ (p + q)) := by rw [pow_add]; ring
    _ = _ := by rw [inv_pow, ← sqrt_nat_pow (Nat.cast_nonneg (Fintype.card α))]; rfl

theorem norm_preservationSum_le (hW : W.card = p + 1 + q)
    (left : Fin p → ι) (middle : ι) (right : Fin q → ι) :
    ‖∑ t : OrderedLabelTuple W (p + 1 + q),
      M.creationWord W left (tupleDropMiddle t).val.1 * M.D middle (tupleMiddle t) *
        M.annihilationWord W right (tupleDropMiddle t).val.2‖ ≤
      (Real.sqrt (p.factorial : ℝ) * Real.sqrt (q.factorial : ℝ)) *
        (1 + (p + q + 1 : ℝ) / Fintype.card α) /
          Real.sqrt ((Fintype.card α : ℝ) ^ (p + q)) := by
  rw [preservation_sum_eq_sandwich W p q hW]
  apply (norm_row_matrix_column_entry_le _ _ _).trans
  have he : orderedMissingLabelMatrix W hW (M.D middle) =
      orderedPreservationMatrix W (p := q) (q := p) (by omega)
        (M.e middle) (M.P middle) (Fintype.card α : ℝ) := by
    exact orderedMissingLabelMatrix_eq_preservation W hW (M.e middle) (M.P middle) _
  have hT : ‖orderedMissingLabelMatrix W hW (M.D middle)‖ ≤
      (Real.sqrt (p.factorial : ℝ) * Real.sqrt (q.factorial : ℝ)) *
        (1 + (p + q + 1 : ℝ) / Fintype.card α) := by
    rw [he]
    apply (norm_orderedPreservationMatrix_le W _ (M.e middle)
      (M.e_projection middle) (M.e_orthogonal middle) (M.P middle) (M.P_projection middle)
      (by exact_mod_cast Fintype.card_pos_iff.mpr ‹Nonempty α›)).trans
    have hs := preservation_scalar_sqrt_le q p
    have hs' : Real.sqrt (((q + 1 : ℕ) : ℝ) * ((p + 1 : ℕ) : ℝ)) ≤
        (p + q + 1 : ℝ) := by simpa only [add_comm (q : ℝ) p] using hs
    calc
      _ = (Real.sqrt (p.factorial : ℝ) * Real.sqrt (q.factorial : ℝ)) *
          (1 + Real.sqrt (((q + 1 : ℕ) : ℝ) * ((p + 1 : ℕ) : ℝ)) / Fintype.card α) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (add_le_add_right (div_le_div_of_nonneg_right hs'
          (Nat.cast_nonneg (Fintype.card α))) 1) (by positivity)
  calc
    _ ≤ ((Real.sqrt (Fintype.card α : ℝ))⁻¹ ^ p) *
        ((Real.sqrt (p.factorial : ℝ) * Real.sqrt (q.factorial : ℝ)) *
          (1 + (p + q + 1 : ℝ) / Fintype.card α)) *
        ((Real.sqrt (Fintype.card α : ℝ))⁻¹ ^ q) := by
      apply mul_le_mul
      · exact mul_le_mul (M.norm_creationWord_row_le W left) hT (norm_nonneg _) (by positivity)
      · exact M.norm_annihilationWord_column_le W right
      · positivity
      · positivity
    _ = ((Real.sqrt (p.factorial : ℝ) * Real.sqrt (q.factorial : ℝ)) *
          (1 + (p + q + 1 : ℝ) / Fintype.card α)) *
        ((Real.sqrt (Fintype.card α : ℝ))⁻¹ ^ (p + q)) := by rw [pow_add]; ring
    _ = _ := by rw [inv_pow, ← sqrt_nat_pow (Nat.cast_nonneg (Fintype.card α))]; rfl

end

end KadisonKastler.FreeDiagonalModel

end OAI
