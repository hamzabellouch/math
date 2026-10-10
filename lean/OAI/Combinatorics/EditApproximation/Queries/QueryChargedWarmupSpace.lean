import OAI.Combinatorics.EditApproximation.Queries.QueryInitialConeSpace
import OAI.Combinatorics.EditApproximation.Queries.QueryIndexedSpace
import OAI.Combinatorics.EditApproximation.Queries.QueryChargedSeedSpace
import OAI.Combinatorics.EditApproximation.Queries.QueryWarmupSpace
import OAI.Combinatorics.EditApproximation.Queries.QueryChargedWarmup

namespace OAI

namespace EditApproximation
open BitQuery

section Initial
variable (source target : List ℕ) {M J passes copies T S : ℕ}
  (N P F : ℕ) (A a : BinaryFraction) (multiplier : ℕ → ℕ)
  (parent : {r : PhysicalTableRequest M J target.length // r.Bounded passes copies T S})
  (occurrence : BinaryMemo PositionCounts) (symbolBits positionBits : ℕ)

def queryPhysicalInitialHeap (q : TargetInterval target.length) :
    Heap (queryPhysicalInitial source target N P F A a multiplier parent occurrence symbolBits positionBits q) := by
  let interval := physicalSourceInterval source.length parent.val.node
  have hl := saturatingSubtractAllocation_le_work interval.hi interval.lo
  have ht := naturalWordLEAllocation_le_work (saturatingSubtractWithWork interval.hi interval.lo).1 [true]
  refine Heap.chargeOf (saturatingSubtractAllocation interval.hi interval.lo +
    naturalWordLEAllocation (saturatingSubtractWithWork interval.hi interval.lo).1 [true]) (by
      dsimp only [interval] at hl ht ⊢
      omega) ?_
  split
  · exact Heap.computeOf _ (queryIndexedSliceAllocation source interval target.length q occurrence symbolBits positionBits)
      (queryIndexedSliceAllocation_le_work source interval target.length q occurrence symbolBits positionBits)
  · exact queryInitialConeProgramAtHeap _ N P F A a (queryChargedSeedAt parent N multiplier) q
      (queryChargedSeedAtHeap parent N multiplier)

def queryChargedWarmupHeap :
    Heap (queryChargedWarmup source target N P F A a multiplier parent occurrence symbolBits positionBits) := by
  have hinit := queryPhysicalInitialHeap source target N P F A a multiplier parent occurrence symbolBits positionBits
  unfold queryChargedWarmup
  refine Heap.chargeOf (naturalEqualAllocation parent.val.index 0)
    ((naturalEqualAllocation_le_work _ _).trans (Nat.le_succ _)) ?_
  split
  · exact hinit _
  · refine Heap.chargeOf (parent.val.node.1.val.bits.length + J.bits.length)
      ((bitCompareWithWork_input_cells _ _).trans (Nat.le_succ _)) ?_
    split
    · let interval := physicalSourceInterval source.length parent.val.node
      have hl := saturatingSubtractAllocation_le_work interval.hi interval.lo
      have ht := naturalWordLEAllocation_le_work (saturatingSubtractWithWork interval.hi interval.lo).1 [true]
      refine Heap.chargeOf (saturatingSubtractAllocation interval.hi interval.lo +
        naturalWordLEAllocation (saturatingSubtractWithWork interval.hi interval.lo).1 [true]) (by
          dsimp only [interval] at hl ht ⊢
          omega) ?_
      split
      · exact hinit _
      · apply queryWarmupProgramHeap
        · exact hinit
        · intro input
          exact queryChargedReadHeap parent _
    · exact hinit _

end Initial
end EditApproximation

end OAI
