import OAI.Combinatorics.EditApproximation.Queries.QueryInitialConeProgram
import OAI.Combinatorics.EditApproximation.Queries.QueryChargedSeed
import OAI.Combinatorics.EditApproximation.Queries.QueryIndexedSlice
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! The complete physical initial branch.  It reads terminal symbols
through the original array and uses a length descriptor for the nonterminal
initial-cone computation.  Seed reads remain adaptive ranked requests. -/

namespace EditApproximation

section Initial
variable (source target : List ℕ) {M J passes copies T S : ℕ}
  (N P F : ℕ) (A a : BinaryFraction) (multiplier : ℕ → ℕ)
  (parent : {r : PhysicalTableRequest M J target.length // r.Bounded passes copies T S})
  (occurrence : BinaryMemo PositionCounts) (symbolBits positionBits : ℕ)
  (q : TargetInterval target.length)



theorem queryPhysicalInitial_refines (hP : 0 < P)
    (ha : a.value = refinementFactor A.value F)
    (hs : ∀ z ∈ source, z < 2 ^ symbolBits) (ht : ∀ z ∈ target, z < 2 ^ symbolBits)
    (hp : target.length ≤ 2 ^ positionBits)
    (htable : occurrence = occurrenceBuild symbolBits positionBits target.zipIdx) :
    BitQuery.Refines (fun word value => word.value = value)
      (queryPhysicalInitial source target N P F A a multiplier parent occurrence symbolBits positionBits q)
      (physicalInitialQuery source target N P F A.value (chargedSeedQuery N multiplier parent)
        (parent.val.node, q)) := by
  have htest : (wordLEWithWork
      (saturatingSubtractWithWork (physicalSourceInterval source.length parent.val.node).hi
        (physicalSourceInterval source.length parent.val.node).lo).1 [true]).1 = true ↔
      (physicalSource source parent.val.node).length ≤ 1 := by
    rw [wordLEWithWork_value, saturatingSubtractWithWork_value, physicalSource_length_eq]
    rfl
  unfold queryPhysicalInitial
  apply BitQuery.Refines.charge
  unfold physicalInitialQuery
  dsimp only
  by_cases hshort : (physicalSource source parent.val.node).length ≤ 1
  · rw [ite_eq_left hshort, ite_eq_left (htest.mpr hshort)]
    apply BitQuery.Refines.charge
    apply BitQuery.Refines.done
    rw [htable, queryIndexedSliceWithWork_value source target _ _ symbolBits positionBits hs ht hp]
    rfl
  · rw [ite_eq_right hshort, ite_eq_right (fun h => hshort (htest.mp h))]
    simp only [saturatingSubtractWithWork_value]
    rw [← physicalSource_length_eq source parent.val.node]
    exact queryInitialConeProgram_refines (physicalSource source parent.val.node) target N P F hP A a
      (queryChargedSeedAt parent N multiplier) q
      (fun r => chargedSeedQuery N multiplier parent (parent.val.node, r))
      (fun r => queryChargedSeedAt_refines parent N multiplier r) ha

end Initial
end EditApproximation

end OAI
