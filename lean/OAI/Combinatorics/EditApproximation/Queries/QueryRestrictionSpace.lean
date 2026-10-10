import OAI.Combinatorics.EditApproximation.Binary.BitQueryKeysSpace
import OAI.Combinatorics.EditApproximation.Queries.QueryGatherSpace
import OAI.Combinatorics.EditApproximation.Queries.QueryBoundedBody
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

namespace EditApproximation



theorem queryPhysicalBoundedAllocation_le_work {M J n : ℕ} (passes copies T S : ℕ)
    (request : PhysicalTableRequest M J n) :
    queryPhysicalBoundedAllocation passes copies T S request ≤ (queryPhysicalBoundedWithWork passes copies T S request).2 := by
  have hp := bitCompareWithWork_input_cells request.pass.bits passes.bits
  have hc := bitCompareWithWork_input_cells request.copy.bits copies.bits
  have ha := binaryNaturalAddAllocation_le_work T S
  have hi := naturalWordLEAllocation_le_work request.index.bits (binaryNaturalAddWithWork T S).1
  unfold queryPhysicalBoundedAllocation queryPhysicalBoundedWithWork
  dsimp only
  unfold binaryNaturalCompareWithWork
  omega



theorem querySupportedChildAllocation_le_work {σ : Type*} {M J n : ℕ} (passes copies T S : ℕ)
    (parent : {r : PhysicalTableRequest M J n // r.Bounded passes copies T S})
    (key : QueryPhysicalChild (σ := σ) passes copies T S parent) :
    querySupportedChildAllocation passes copies T S parent key ≤ (querySupportedChildWithWork passes copies T S parent key).2 := by
  cases key with
  | inl source => exact Nat.zero_le _
  | inr child => exact queryPhysicalBoundedAllocation_le_work passes copies T S child.val

open BitQuery

def queryRestrictPhysicalBodyHeap {σ : Type*} {M J n : ℕ} (passes copies T S : ℕ)
    (parent : {r : PhysicalTableRequest M J n // r.Bounded passes copies T S})
    (program : BitQuery (QueryPhysicalChild (σ := σ) passes copies T S parent) BinaryFraction)
    (heap : Heap program) : Heap (queryRestrictPhysicalBody passes copies T S parent program) :=
  (heap.restrictWithWork _ _ (querySupportedChildWithWork_value passes copies T S parent)
    (querySupportedChildAllocation passes copies T S parent)
    (querySupportedChildAllocation_le_work passes copies T S parent)).mapKeysWithWork _ (fun _ => 1) (fun _ => le_rfl)

end EditApproximation

end OAI
