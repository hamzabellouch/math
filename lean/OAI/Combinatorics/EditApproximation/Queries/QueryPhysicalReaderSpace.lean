import OAI.Combinatorics.EditApproximation.Queries.QueryLocalProgramSpace
import OAI.Combinatorics.EditApproximation.Binary.BitQueryKeysSpace
import OAI.Combinatorics.EditApproximation.Queries.QueryPhysicalProgram
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

namespace EditApproximation

/-- Scalar RAM cells created by the node-code recurrence, two powers and
entry/table arithmetic. The path and input request are borrowed. -/


theorem physicalTableCodeAllocation_le_work {M J n : ℕ} (copies T S : ℕ)
    (request : PhysicalTableRequest M J n) :
    physicalTableCodeAllocation request ≤ (physicalTableCodeWithWork copies T S request).2 := by
  have tableBound (d J : ℕ) :
      2 * d + 2 * J + 20 ≤
        3 * d + 1 + (2 * J + 1) + 3 + 8 + (2 * J + 1) + 15 := by
    omega
  simp only [physicalTableCodeAllocation, physicalTableCodeWithWork, physicalEntryCodeWithWork,
    physicalNodeCodeWithWork, treeLayerCodeWithWork_cost, parameterPowerWithWork_spec]
  exact tableBound _ _

open BitQuery

def queryPhysicalTableReadHeap {M J n : ℕ} (copies T S : ℕ)
    (parent : PhysicalTableRequest M J n)
    (child : {r : PhysicalTableRequest M J n // r.combinedRank T S < parent.combinedRank T S}) :
    Heap (queryPhysicalTableRead copies T S parent child) :=
  Heap.chargeOf (physicalTableCodeAllocation child.val + 1)
    (Nat.add_le_add_right (physicalTableCodeAllocation_le_work copies T S child.val) 1)
    (.read child _ fun word => .done word)

def queryMeanReadHeap {ι : Type*} (count : ℕ) (reader : Fin count → BitQuery ι BinaryFraction)
    (hr : ∀ i, Heap (reader i)) : Heap (queryMeanRead count reader) := by
  refine Heap.chargeOf count (by omega) (Heap.collect reader hr _ _ fun words => ?_)
  refine Heap.computeOf (BinaryFraction.queryMeanWithWork count words)
    (BinaryFraction.sumListAllocation words + BinaryFraction.divAllocation
      (BinaryFraction.sumListWithWork words).1 (BinaryFraction.nat count) + Nat.size count) ?_
  have hs := BinaryFraction.sumListAllocation_le_work words
  have hd := BinaryFraction.divAllocation_le_work (BinaryFraction.sumListWithWork words).1 (BinaryFraction.nat count)
  unfold BinaryFraction.queryMeanWithWork
  dsimp only
  omega

def queryPhysicalEarlierReadHeap {M J n : ℕ} (copies pass copy T S t : ℕ)
    (node : PhysicalNode M J) (hbelow : node.1.val < J) (q : TargetInterval n)
    (input : Fin M × ℕ × TargetInterval n) :
    Heap (queryPhysicalEarlierRead copies pass copy T S t node hbelow q input) := by
  refine Heap.chargeOf (input.2.1.bits.length + t.bits.length) ?_ ?_
  · exact (bitCompareWithWork_input_cells _ _).trans (Nat.le_succ _)
  · split
    · exact queryPhysicalTableReadHeap copies T S _ _
    · exact .done _

def queryPhysicalRandomDataRequestHeap {σ α : Type*} (source target : List α) {M J : ℕ} [NeZero M]
    (N P F exponent H Q eM eF : ℕ) (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
    (tau a eta kappa delta : BinaryFraction) (copies pass copy T S t : ℕ) (ht : 0 < t)
    (node : PhysicalNode M J) (hbelow : node.1.val < J)
    (readGroup : GroupScalarKey M F Q → BitQuery σ BinaryFraction)
    (readInteger : (ℕ × TargetInterval target.length) → ℕ → BitQuery σ BinaryFraction)
    (q : TargetInterval target.length)
    (hg : ∀ key, Heap (readGroup key)) (hz : ∀ key range, Heap (readInteger key range)) :
    Heap (queryPhysicalRandomDataRequest source target N P F exponent H Q eM eF hP hM hF
      tau a eta kappa delta copies pass copy T S t ht node hbelow readGroup readInteger q) := by
  unfold queryPhysicalRandomDataRequest
  apply queryLocalProgramHeap
  · intro r
    exact (queryPhysicalTableReadHeap copies T S _ _).mapKeysWithWork _ (fun _ => 1) (fun _ => le_rfl)
  · intro input
    apply Heap.mapKeysWithWork _ (fun _ => 1) (fun _ => le_rfl)
    apply queryMeanReadHeap
    intro j
    exact queryPhysicalTableReadHeap copies T S _ _
  · intro input
    exact (queryPhysicalTableReadHeap copies T S _ _).mapKeysWithWork _ (fun _ => 1) (fun _ => le_rfl)
  · intro key
    exact (hg key).mapKeysWithWork _ (fun _ => 1) (fun _ => le_rfl)
  · intro key range
    exact (hz key range).mapKeysWithWork _ (fun _ => 1) (fun _ => le_rfl)
  · intro input
    exact (queryPhysicalEarlierReadHeap copies pass copy T S t node hbelow q input).mapKeysWithWork _
      (fun _ => 1) (fun _ => le_rfl)
  · intro input
    exact (queryPhysicalTableReadHeap copies T S _ _).mapKeysWithWork _ (fun _ => 1) (fun _ => le_rfl)

end EditApproximation

end OAI
