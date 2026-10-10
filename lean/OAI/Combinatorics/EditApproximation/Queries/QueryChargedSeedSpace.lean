import OAI.Combinatorics.EditApproximation.Queries.QueryPhysicalReaderSpace
import OAI.Combinatorics.EditApproximation.Queries.QueryChargedSeed
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

namespace EditApproximation

/-- Scalar cells of the actual coarse/table address construction. -/


theorem chargedPhysicalCodeAllocation_le_work {M J n passes copies T S : ℕ}
    (request : ChargedPhysicalRequest M J n passes copies T S) :
    chargedPhysicalCodeAllocation request ≤ (chargedPhysicalCodeWithWork request).2 := by
  have entryBound (d J : ℕ) :
      2 * d + J + 12 ≤ 3 * d + 1 + (2 * J + 1) + 3 + 8 + 2 := by
    omega
  cases request with
  | inl entry =>
    simp only [chargedPhysicalCodeAllocation, chargedPhysicalCodeWithWork, physicalEntryCodeWithWork,
      physicalNodeCodeWithWork, treeLayerCodeWithWork_cost, parameterPowerWithWork_spec]
    exact entryBound _ _
  | inr request =>
    have h := physicalTableCodeAllocation_le_work copies T S request.val
    change physicalTableCodeAllocation request.val + 2 ≤ (physicalTableCodeWithWork copies T S request.val).2 + 3
    exact Nat.add_le_add h (by decide : 2 ≤ 3)

open BitQuery

section Seed
variable {M J n passes copies T S : ℕ}
  (parent : {r : PhysicalTableRequest M J n // r.Bounded passes copies T S})

def queryChargedReadHeap
    (key : {child : ChargedPhysicalRequest M J n passes copies T S //
      child.rank < ChargedPhysicalRequest.rank (.inr parent)}) : Heap (queryChargedRead parent key) :=
  Heap.chargeOf (chargedPhysicalCodeAllocation key.val + 1)
    (Nat.add_le_add_right (chargedPhysicalCodeAllocation_le_work key.val) 1) (.read key _ fun word => .done word)

def queryChargedSeedAtHeap (N : ℕ) (multiplier : ℕ → ℕ) (q : TargetInterval n) :
    Heap (queryChargedSeedAt parent N multiplier q) := by
  refine Heap.chargeOf (naturalEqualAllocation parent.val.pass 0)
    ((naturalEqualAllocation_le_work _ _).trans (Nat.le_succ _)) ?_
  split
  · exact queryChargedReadHeap parent _
  · refine Heap.chargeOf copies (Nat.le_succ _) ?_
    refine Heap.collect _ (fun _ => queryChargedReadHeap parent _) _ _ fun words => ?_
    let factor := multiplier (parent.val.pass - 1)
    refine Heap.computeOf (BinaryFraction.querySeedMedianWithWork N factor words)
      (BinaryFraction.seedMedianAllocation N factor words + (BinaryFraction.seedMedianWithWork N factor words).1.length + 1) ?_
    have hm := BinaryFraction.seedMedianAllocation_le_work N factor words
    unfold BinaryFraction.querySeedMedianWithWork
    dsimp only
    omega

end Seed
end EditApproximation

end OAI
