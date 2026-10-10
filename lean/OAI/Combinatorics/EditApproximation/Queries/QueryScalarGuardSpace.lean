import OAI.Combinatorics.EditApproximation.Binary.BinaryInitialGuardSpace
import OAI.Combinatorics.EditApproximation.Queries.QueryPhysicalScalarGuards
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

namespace EditApproximation



theorem queryNaturalIndexAllocation_le_work (a : ℕ) (xs : List ℕ) :
    queryNaturalIndexAllocation a xs ≤ (queryNaturalIndexWithWork a xs).2 := by
  induction xs with
  | nil => exact Nat.zero_le _
  | cons b rest ih =>
    have he := naturalEqualAllocation_le_work a b
    simp only [queryNaturalIndexAllocation, queryNaturalIndexWithWork]
    split_ifs <;> dsimp only <;> omega



theorem queryScaleDispatchAllocation_le_work (N b : ℕ) :
    queryScaleDispatchAllocation N b ≤ (queryScaleDispatchWithWork N b).2 := by
  have hd := dyadicScalesAllocation_le_work N
  have hi := queryNaturalIndexAllocation_le_work b (dyadicScalesWithWork N).1
  unfold queryScaleDispatchAllocation queryScaleDispatchWithWork
  dsimp only
  omega



theorem queryScalePresentAllocation_le_work (N b : ℕ) :
    queryScalePresentAllocation N b ≤ (queryScalePresentWithWork N b).2 := by
  have hd := queryScaleDispatchAllocation_le_work N b
  have hc := bitCompareWithWork_input_cells (queryScaleDispatchWithWork N b).1.bits (max 1 N.bits.length).bits
  unfold queryScalePresentAllocation queryScalePresentWithWork
  dsimp only
  change _ ≤ _ + (bitCompareWithWork (queryScaleDispatchWithWork N b).1.bits (max 1 N.bits.length).bits).2 + 2
  omega



theorem queryCellValidAllocation_le_work (n exponent : ℕ) (cell : ℕ × ℕ) :
    queryCellValidAllocation n exponent cell ≤ (queryCellValidWithWork n exponent cell).2 := by
  have hm := binaryNaturalMulAllocation_le_work n (bitWordValue (powerTwoWord exponent))
  have hl := naturalWordLEAllocation_le_work cell.1.bits (binaryNaturalMulWithWork n (bitWordValue (powerTwoWord exponent))).1
  have hr := naturalWordLEAllocation_le_work cell.2.bits (binaryNaturalMulWithWork n (bitWordValue (powerTwoWord exponent))).1
  unfold queryCellValidAllocation queryCellValidWithWork
  dsimp only
  omega



theorem queryRangeValidAllocation_le_work (B range : ℕ) :
    queryRangeValidAllocation B range ≤ (queryRangeValidWithWork B range).2 := by
  have hp := bitCompareWithWork_input_cells (0 : ℕ).bits range.bits
  have hb := naturalWordLEAllocation_le_work range.bits B.bits
  unfold queryRangeValidAllocation queryRangeValidWithWork
  dsimp only
  change _ ≤ (bitCompareWithWork (0 : ℕ).bits range.bits).2 + _ + 2
  omega

end EditApproximation

end OAI
