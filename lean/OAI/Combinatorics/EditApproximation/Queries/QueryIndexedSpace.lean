import OAI.Combinatorics.EditApproximation.Queries.QueryGatherSpace
import OAI.Combinatorics.EditApproximation.Queries.QueryIndexedSlice
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

namespace EditApproximation

/-- The occurrence key, two prefix traversals and scalar result cells.
The occurrence trie itself is borrowed from preprocessing. -/


theorem indexedLeafAllocation_le_work (table : BinaryMemo PositionCounts) (symbolBits positionBits : ℕ)
    (symbol : Option ℕ) (lo hi : ℕ) :
    indexedLeafAllocation symbolBits positionBits symbol lo hi ≤
      (indexedLeafWithWork table symbolBits positionBits symbol lo hi).2 := by
  cases symbol with
  | none => change 1 ≤ 2; omega
  | some a =>
    unfold indexedLeafAllocation indexedLeafWithWork indexedSingletonCostWithWork
    split_ifs <;> simp only [occurrenceQueryWithWork_spec] <;> omega



theorem binaryIndexedLeafAllocation_le_work (table : BinaryMemo PositionCounts) (symbolBits positionBits : ℕ)
    (symbol : Option ℕ) (lo hi : ℕ) :
    binaryIndexedLeafAllocation table symbolBits positionBits symbol lo hi ≤
      (binaryIndexedLeafWithWork table symbolBits positionBits symbol lo hi).2 :=
  Nat.add_le_add_right (Nat.add_le_add_right (indexedLeafAllocation_le_work table symbolBits positionBits symbol lo hi) _) _



theorem queryIndexedSliceAllocation_le_work (source : List ℕ) (interval : TargetInterval source.length)
    (targetLength : ℕ) (q : TargetInterval targetLength)
    (occurrence : BinaryMemo PositionCounts) (symbolBits positionBits : ℕ) :
    queryIndexedSliceAllocation source interval targetLength q occurrence symbolBits positionBits ≤
      (queryIndexedSliceWithWork source interval targetLength q occurrence symbolBits positionBits).2 := by
  have hc := bitCompareWithWork_input_cells interval.lo.bits interval.hi.bits
  have hl := binaryIndexedLeafAllocation_le_work occurrence symbolBits positionBits
    (querySliceHeadWithWork source interval).1 q.lo q.hi
  have hs : interval.lo.bits.length + interval.hi.bits.length + 1 ≤
      (querySliceHeadWithWork source interval).2 := by
    unfold querySliceHeadWithWork
    dsimp only
    change _ ≤ (bitCompareWithWork interval.lo.bits interval.hi.bits).2 + _ + _ + 3
    omega
  unfold queryIndexedSliceAllocation queryIndexedSliceWithWork
  dsimp only
  omega

end EditApproximation

end OAI
