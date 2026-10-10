import OAI.Combinatorics.EditApproximation.Binary.BitQuery
import OAI.Combinatorics.EditApproximation.Geometry.ChargedSeedQuery
import OAI.Combinatorics.EditApproximation.Binary.BinaryInitialKernel
import OAI.Combinatorics.EditApproximation.Binary.BinarySeedMedianWork
import OAI.Combinatorics.EditApproximation.Geometry.MemoCodeWork
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Seed values are computed by actual coarse-cache or previous-pass
requests.  The copy median and the pass-zero test have explicit work. -/

namespace EditApproximation
namespace BinaryFraction



@[simp] theorem querySeedMedianWithWork_value (N multiplier : ℕ) (words : List BinaryFraction) :
    (querySeedMedianWithWork N multiplier words).1.value =
      (min N (upperMedian (words.map fun word => ⌈(multiplier : ℚ) * word.value⌉₊)) : ℕ) := by
  simp only [querySeedMedianWithWork, ofNaturalWord_value, seedMedianWithWork_value]

end BinaryFraction

section Seed
variable {M J n passes copies T S : ℕ}
  (parent : {r : PhysicalTableRequest M J n // r.Bounded passes copies T S})



theorem queryChargedRead_refines
    (key : {child : ChargedPhysicalRequest M J n passes copies T S //
      child.rank < ChargedPhysicalRequest.rank (.inr parent)}) :
    BitQuery.Refines (fun word value => word.value = value) (queryChargedRead parent key) (.read key .done) :=
  .charge _ (.read key _ _ (fun _ => .done rfl))



theorem queryChargedPreviousRead_refines (hp : 0 < parent.val.pass) (q : TargetInterval n)
    (copy : Fin copies) :
    BitQuery.Refines (fun word value => word.value = value)
      (queryChargedPreviousRead parent hp q copy) (chargedPreviousRead parent hp q copy) :=
  queryChargedRead_refines parent _



theorem queryChargedSeedAt_refines (N : ℕ) (multiplier : ℕ → ℕ) (q : TargetInterval n) :
    BitQuery.Refines (fun word value => word.value = value)
      (queryChargedSeedAt parent N multiplier q)
      (chargedSeedQuery N multiplier parent (parent.val.node, q)) := by
  unfold queryChargedSeedAt chargedSeedQuery
  rw [dite_eq_left rfl]
  apply BitQuery.Refines.charge
  by_cases hp : parent.val.pass = 0
  · rw [dite_eq_left hp, dite_eq_left ((naturalEqualWithWork_value _ _).mpr hp)]
    exact queryChargedRead_refines parent _
  · rw [dite_eq_right hp, dite_eq_right (fun h => hp ((naturalEqualWithWork_value _ _).mp h))]
    apply BitQuery.Refines.charge
    apply BitQuery.Refines.collect _ _ (fun copy => queryChargedPreviousRead_refines parent _ q copy)
    intro words
    apply BitQuery.Refines.charge
    apply BitQuery.Refines.done
    simp only [BinaryFraction.querySeedMedianWithWork_value, List.map_map, Function.comp_def]

end Seed
end EditApproximation

end OAI
