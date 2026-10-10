import OAI.Combinatorics.EditApproximation.Queries.QueryScalarDispatch
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Executed natural-word guards for finite physical source requests. -/

namespace EditApproximation



@[simp] theorem queryScalePresentWithWork_value (N b : ℕ) :
    (queryScalePresentWithWork N b).1 = true ↔ b ∈ dyadicScales N := by
  simp only [queryScalePresentWithWork, decide_eq_true_eq, binaryNaturalCompareWithWork_lt,
    queryScaleDispatchWithWork_value]
  have hl : (dyadicScales N).length = max 1 N.bits.length := by
    rw [← dyadicScalesWithWork_value N]
    simp only [dyadicScalesWithWork, arithmeticMapWithWork_value, List.length_map, List.length_range]
  rw [← hl]
  exact List.idxOf_lt_length_iff



@[simp] theorem queryCellValidWithWork_value (n exponent : ℕ) (cell : ℕ × ℕ) :
    (queryCellValidWithWork n exponent cell).1 = true ↔
      cell.1 ≤ n * 2 ^ exponent ∧ cell.2 ≤ n * 2 ^ exponent := by
  simp only [queryCellValidWithWork, Bool.and_eq_true, wordLEWithWork_value, bitWordValue_bits,
    binaryNaturalMulWithWork_value, powerTwoWord_value]



@[simp] theorem queryRangeValidWithWork_value (B range : ℕ) :
    (queryRangeValidWithWork B range).1 = true ↔ 0 < range ∧ range ≤ B := by
  simp only [queryRangeValidWithWork, Bool.and_eq_true, decide_eq_true_eq,
    binaryNaturalCompareWithWork_lt, wordLEWithWork_value, bitWordValue_bits]

end EditApproximation

end OAI
