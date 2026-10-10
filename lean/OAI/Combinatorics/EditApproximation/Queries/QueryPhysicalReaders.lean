import OAI.Combinatorics.EditApproximation.Queries.QueryMeanRead
import OAI.Combinatorics.EditApproximation.Binary.BitQueryKeys
import OAI.Combinatorics.EditApproximation.Geometry.MemoCodeWork
import OAI.Combinatorics.EditApproximation.Refinement.PhysicalRandomDataRequest
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Actual ranked physical reads for the charged local program.  Table
addresses are constructed before lookup, mass reads execute their mean,
and the total history reader executes its natural-word guard. -/

namespace EditApproximation



theorem queryPhysicalTableRead_refines {M J n : ℕ} (copies T S : ℕ)
    (parent : PhysicalTableRequest M J n)
    (child : {r : PhysicalTableRequest M J n // r.combinedRank T S < parent.combinedRank T S}) :
    BitQuery.Refines (fun word value => word.value = value)
      (queryPhysicalTableRead copies T S parent child) (.read child .done) :=
  .charge _ (.read child _ _ (fun _ => .done rfl))

theorem queryPhysicalTableRead_work {M J n : ℕ} (copies T S : ℕ)
    (parent : PhysicalTableRequest M J n)
    (child : {r : PhysicalTableRequest M J n // r.combinedRank T S < parent.combinedRank T S})
    (oracle : {r : PhysicalTableRequest M J n // r.combinedRank T S < parent.combinedRank T S} → BinaryFraction)
    (readWork : {r : PhysicalTableRequest M J n // r.combinedRank T S < parent.combinedRank T S} → ℕ) :
    (queryPhysicalTableRead copies T S parent child).work oracle readWork ≤
      7 * J + 30 + readWork child := by
  have h := physicalTableCodeWithWork_cost copies T S child.val
  change _ + 1 + (readWork child + 0) ≤ _
  omega



theorem queryPhysicalWarmupRead_refines {M J n : ℕ} (copies pass copy T S t : ℕ) (ht : 0 < t)
    (node : PhysicalNode M J) (q : TargetInterval n)
    (otherNode : PhysicalNode M J) (hnode : node.1.val ≤ otherNode.1.val)
    (j : ℕ) (hj : j ≤ T) (r : TargetInterval n) :
    BitQuery.Refines (fun word value => word.value = value)
      (queryPhysicalWarmupRead copies pass copy T S t ht node q otherNode hnode j hj r)
      (physicalRefinementWarmupRead pass copy T S t ht node q otherNode hnode j hj r) :=
  queryPhysicalTableRead_refines copies T S _ _



theorem queryPhysicalMassRead_refines {M J n : ℕ} (copies pass copy T S t : ℕ) (ht : 0 < t)
    (node : PhysicalNode M J) (hbelow : node.1.val < J) (q : TargetInterval n)
    (input : Fin M × TargetInterval n) :
    BitQuery.Refines (fun word value => word.value = value)
      (queryPhysicalMassRead copies pass copy T S t ht node hbelow q input)
      (physicalRefinementMassQuery pass copy T S t ht node hbelow q input) :=
  queryMeanRead_refines T _ _ (fun _ => queryPhysicalWarmupRead_refines copies pass copy T S t ht
    node q _ _ _ _ _)



theorem queryPhysicalCurrentRead_refines {M J n : ℕ} (copies pass copy T S t : ℕ)
    (node : PhysicalNode M J) (hbelow : node.1.val < J) (q : TargetInterval n)
    (input : Fin M × TargetInterval n) :
    BitQuery.Refines (fun word value => word.value = value)
      (queryPhysicalCurrentRead copies pass copy T S t node hbelow q input)
      (physicalRefinementCurrentQuery pass copy T S t node hbelow q input) :=
  queryPhysicalTableRead_refines copies T S _ _



theorem queryPhysicalEarlierRead_refines {M J n : ℕ} (copies pass copy T S t : ℕ)
    (node : PhysicalNode M J) (hbelow : node.1.val < J) (q : TargetInterval n)
    (input : Fin M × ℕ × TargetInterval n) :
    BitQuery.Refines (fun word value => word.value = value)
      (queryPhysicalEarlierRead copies pass copy T S t node hbelow q input)
      (physicalRefinementEarlierQuery pass copy T S t node hbelow q input) := by
  unfold queryPhysicalEarlierRead
  apply BitQuery.Refines.charge
  unfold physicalRefinementEarlierQuery
  by_cases hs : input.2.1 < t
  · rw [dite_eq_left hs, dite_eq_left ((binaryNaturalCompareWithWork_lt _ _).mpr hs)]
    exact queryPhysicalTableRead_refines copies T S _ _
  · rw [dite_eq_right hs, dite_eq_right (fun h => hs ((binaryNaturalCompareWithWork_lt _ _).mp h))]
    exact .done (by simp only [BinaryFraction.nat_value, Nat.cast_zero])

end EditApproximation

end OAI
