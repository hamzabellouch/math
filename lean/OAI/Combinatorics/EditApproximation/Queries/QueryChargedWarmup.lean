import OAI.Combinatorics.EditApproximation.Queries.QueryPhysicalInitial
import OAI.Combinatorics.EditApproximation.Queries.QueryWarmupProgram
import OAI.Combinatorics.EditApproximation.Geometry.ChargedGlobalQuery
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Executed warmup dispatch and ranked child reads.  Both the terminal
and positive-depth branches use the same adaptive initial-cone program. -/

namespace EditApproximation

section Child
variable {M J ny passes copies T S : ℕ}
  (parent : {r : PhysicalTableRequest M J ny // r.Bounded passes copies T S})
  (hbelow : parent.val.node.1.val < J) (hindex : 0 < parent.val.index)
  (input : Fin M × TargetInterval ny)



theorem queryChargedWarmupChild_refines :
    BitQuery.Refines (fun word value => word.value = value)
      (queryChargedWarmupChild parent hbelow hindex input)
      (chargedWarmupChild parent hbelow hindex input) :=
  queryChargedRead_refines parent _

end Child

section Warmup
variable (source target : List ℕ) {M J passes copies T S : ℕ}
  (N P F : ℕ) (A a : BinaryFraction) (multiplier : ℕ → ℕ)
  (parent : {r : PhysicalTableRequest M J target.length // r.Bounded passes copies T S})
  (occurrence : BinaryMemo PositionCounts) (symbolBits positionBits : ℕ)



theorem queryChargedWarmup_refines (factor : ℕ → ℚ) (hA : A.value = factor parent.val.pass) (hP : 0 < P)
    (ha : a.value = refinementFactor A.value F)
    (hs : ∀ z ∈ source, z < 2 ^ symbolBits) (ht : ∀ z ∈ target, z < 2 ^ symbolBits)
    (hp : target.length ≤ 2 ^ positionBits)
    (htable : occurrence = occurrenceBuild symbolBits positionBits target.zipIdx) :
    BitQuery.Refines (fun word value => word.value = value)
      (queryChargedWarmup source target N P F A a multiplier parent occurrence symbolBits positionBits)
      (chargedWarmupQuery source target N P F factor multiplier parent) := by
  have hi (q : TargetInterval target.length) := queryPhysicalInitial_refines source target N P F A a
    multiplier parent occurrence symbolBits positionBits q hP ha hs ht hp htable
  unfold queryChargedWarmup chargedWarmupQuery
  rw [← hA]
  apply BitQuery.Refines.charge
  by_cases hz : parent.val.index = 0
  · rw [dite_eq_left hz, dite_eq_left ((naturalEqualWithWork_value _ _).mpr hz)]
    exact hi _
  · rw [dite_eq_right hz, dite_eq_right (fun h => hz ((naturalEqualWithWork_value _ _).mp h))]
    apply BitQuery.Refines.charge
    by_cases hb : parent.val.node.1.val < J
    · rw [dite_eq_left hb, dite_eq_left ((binaryNaturalCompareWithWork_lt _ _).mpr hb)]
      dsimp only
      apply BitQuery.Refines.charge
      have htest : (wordLEWithWork
          (saturatingSubtractWithWork (physicalSourceInterval source.length parent.val.node).hi
            (physicalSourceInterval source.length parent.val.node).lo).1 [true]).1 = true ↔
          (physicalSourceInterval source.length parent.val.node).hi -
            (physicalSourceInterval source.length parent.val.node).lo ≤ 1 := by
        rw [wordLEWithWork_value, saturatingSubtractWithWork_value]
        rfl
      by_cases hshort : (physicalSourceInterval source.length parent.val.node).hi -
          (physicalSourceInterval source.length parent.val.node).lo ≤ 1
      · rw [ite_eq_left hshort, ite_eq_left (htest.mpr hshort)]
        exact hi _
      · rw [ite_eq_right hshort, ite_eq_right (fun h => hshort (htest.mp h))]
        unfold physicalWarmupStepQuery
        rw [← ha]
        exact queryWarmupProgram_refines _ N P F hP a _ _ _ _ _ hi
          (fun input => queryChargedWarmupChild_refines parent hb _ input)
    · rw [dite_eq_right hb, dite_eq_right (fun h => hb ((binaryNaturalCompareWithWork_lt _ _).mp h))]
      exact hi _

end Warmup
end EditApproximation

end OAI
