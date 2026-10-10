import OAI.Combinatorics.EditApproximation.Queries.QueryScalarGuardSpace
import OAI.Combinatorics.EditApproximation.Queries.QueryPhysicalReaderSpace
import OAI.Combinatorics.EditApproximation.Queries.QueryFamilyScalarReads
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

namespace EditApproximation

private theorem naturalPairWithWork_lower (a b : ℕ) : 4 ≤ (naturalPairWithWork a b).2 := by
  unfold naturalPairWithWork
  split_ifs <;> omega

/-- Address-recurrence and pairing cells; source data and node paths are borrowed. -/


theorem physicalScalarCodeAllocation_le_work {M J N n exponent F Q R B : ℕ}
    (key : PhysicalScalarKey M J N n exponent F Q R B) :
    physicalScalarCodeAllocation key ≤ (physicalScalarCodeWithWork key).2 := by
  have onlineBound (d J a b c : ℕ) (ha : 4 ≤ a) (hb : 4 ≤ b) (hc : 4 ≤ c) :
      2 * d + J + 20 ≤ 3 * d + 1 + (2 * J + 1) + 3 + 8 + a + b + c + 2 := by
    omega
  have groupBound (d J a b c e f g : ℕ)
      (ha : 4 ≤ a) (hb : 4 ≤ b) (hc : 4 ≤ c) (he : 4 ≤ e) (hf : 4 ≤ f) (hg : 4 ≤ g) :
      2 * d + J + 25 ≤ 3 * d + 1 + (2 * J + 1) + 3 + a + b + c + e + f + g + 3 := by
    omega
  rcases key with ⟨online | group, index⟩
  · have h1 := naturalPairWithWork_lower online.2.val.val index.val
    have h2 := naturalPairWithWork_lower online.1.2.1.val (naturalPairWithWork online.2.val.val index.val).1
    have h3 := naturalPairWithWork_lower (physicalEntryCodeWithWork (online.1.1.val, online.1.2.2)).1
      (naturalPairWithWork online.1.2.1.val (naturalPairWithWork online.2.val.val index.val).1).1
    simp only [physicalScalarCodeAllocation, physicalScalarCodeWithWork, physicalEntryCodeWithWork,
      physicalNodeCodeWithWork, treeLayerCodeWithWork_cost, parameterPowerWithWork_spec] at h3 ⊢
    exact onlineBound _ _ _ _ _ h1 h2 h3
  · have h1 := naturalPairWithWork_lower index.2.1.val index.2.2.val
    have h2 := naturalPairWithWork_lower index.1.val (naturalPairWithWork index.2.1.val index.2.2.val).1
    have h3 := naturalPairWithWork_lower group.2.2.2.val
      (naturalPairWithWork index.1.val (naturalPairWithWork index.2.1.val index.2.2.val).1).1
    have h4 := naturalPairWithWork_lower group.2.2.1.val
      (naturalPairWithWork group.2.2.2.val (naturalPairWithWork index.1.val (naturalPairWithWork index.2.1.val index.2.2.val).1).1).1
    have h5 := naturalPairWithWork_lower group.2.1.val
      (naturalPairWithWork group.2.2.1.val (naturalPairWithWork group.2.2.2.val
        (naturalPairWithWork index.1.val (naturalPairWithWork index.2.1.val index.2.2.val).1).1).1).1
    have h6 := naturalPairWithWork_lower (physicalNodeCodeWithWork group.1.val).1
      (naturalPairWithWork group.2.1.val (naturalPairWithWork group.2.2.1.val
        (naturalPairWithWork group.2.2.2.val (naturalPairWithWork index.1.val
          (naturalPairWithWork index.2.1.val index.2.2.val).1).1).1).1).1
    simp only [physicalScalarCodeAllocation, physicalScalarCodeWithWork,
      physicalNodeCodeWithWork, treeLayerCodeWithWork_cost, parameterPowerWithWork_spec] at h6 ⊢
    exact groupBound _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 h6

open BitQuery

section Scalar
variable (M J N n exponent F Q R B : ℕ)

def queryPhysicalScalarReadHeap (key : PhysicalScalarKey M J N n exponent F Q R B) :
    Heap (queryPhysicalScalarRead M J N n exponent F Q R B key) :=
  Heap.chargeOf (physicalScalarCodeAllocation key + 1)
    (Nat.add_le_add_right (physicalScalarCodeAllocation_le_work key) 1) (.read key _ fun word => .done word)

private def groupHeapTransport (b c : ℕ) (h : b = c)
    (actual : BitPhysicalGroupQueries M J N n exponent F Q R B b)
    (heap : ∀ s j, Heap (actual s j)) :
    ∀ s j, Heap ((Eq.mp (congrArg (BitPhysicalGroupQueries M J N n exponent F Q R B) h) actual) s j) := by
  cases h
  exact heap

def queryPhysicalScalarGroupQueriesHeap (node : PhysicalInternalNode M J) (time : Fin R)
    (b : ℕ) (cell : ℕ × ℕ) :
    ∀ s j, Heap (queryPhysicalScalarGroupQueries M J N n exponent F Q R B node time b cell s j) := by
  intro s j
  refine (congrArg BitQuery.Heap (congrArg
    (fun f : BitPhysicalGroupQueries M J N n exponent F Q R B b => f s j)
    (queryPhysicalScalarGroupQueries.eq_1 M J N n exponent F Q R B node time b cell))).mpr ?_
  split
  · rename_i hb
    split
    · rename_i hc
      let key : PhysicalLocalGroupKey M J N n exponent :=
        (node, physicalScaleIndex N b ((queryScalePresentWithWork_value N b).mp hb),
          ⟨cell.1, Nat.lt_succ_of_le ((queryCellValidWithWork_value n exponent cell).mp hc).1⟩,
          ⟨cell.2, Nat.lt_succ_of_le ((queryCellValidWithWork_value n exponent cell).mp hc).2⟩)
      exact groupHeapTransport M J N n exponent F Q R B _ _
        (physicalScaleIndex_get N b ((queryScalePresentWithWork_value N b).mp hb))
        (queryPhysicalScalarGroupQueriesAt M J N n exponent F Q R B key time)
        (fun s j => (congrArg BitQuery.Heap
          (queryPhysicalScalarGroupQueriesAt.eq_1 M J N n exponent F Q R B key time s j)).mpr
            (queryPhysicalScalarReadHeap M J N n exponent F Q R B
              ⟨Sum.inr key, ⟨time, ⟨s, j⟩⟩⟩)) s j
    · exact .done _
  · exact .done _

def queryPhysicalScalarGroupReadHeap (node : PhysicalInternalNode M J) (time : Fin R)
    (key : GroupScalarKey M F Q) : Heap (queryPhysicalScalarGroupRead M J N n exponent F Q R B node time key) :=
  Heap.chargeOf (queryScalePresentAllocation N key.1.1 + queryCellValidAllocation n exponent key.1.2)
    (by have h1 := queryScalePresentAllocation_le_work N key.1.1
        have h2 := queryCellValidAllocation_le_work n exponent key.1.2
        omega)
    (queryPhysicalScalarGroupQueriesHeap M J N n exponent F Q R B node time key.1.1 key.1.2 key.2.1 key.2.2)

def queryPhysicalScalarOnlineReadHeap (node : PhysicalInternalNode M J) (time : Fin R)
    (key : ℕ × TargetInterval n) (range : ℕ) :
    Heap (queryPhysicalScalarOnlineRead M J N n exponent F Q R B node time key range) := by
  refine (congrArg BitQuery.Heap
    (queryPhysicalScalarOnlineRead.eq_1 M J N n exponent F Q R B node time key range)).mpr ?_
  refine BitQuery.Heap.chargeOf (queryScalePresentAllocation N key.1 + queryRangeValidAllocation B range) ?_ ?_
  · have h1 := queryScalePresentAllocation_le_work N key.1
    have h2 := queryRangeValidAllocation_le_work B range
    omega
  · split
    · rename_i hb
      split
      · rename_i hr
        exact queryPhysicalScalarReadHeap M J N n exponent F Q R B
          ⟨.inl ((node, physicalScaleIndex N key.1 ((queryScalePresentWithWork_value N key.1).mp hb), key.2),
            positiveDrawRangeOfLE B range ((queryRangeValidWithWork_value B range).mp hr).1
              ((queryRangeValidWithWork_value B range).mp hr).2), time⟩
      · exact .done _
    · exact .done _

end Scalar

section Family
variable {α : Type*} {M J R : ℕ} (target : List α)
  (N P F exponent H Q passes copies pass copy : ℕ)



theorem queryFamilyTagAllocation_le_work
    (scalar : PhysicalScalarKey M J N target.length exponent F Q R (localOnlineMassBound M P H)) :
    queryFamilyTagAllocation target N P F exponent H Q passes copies pass copy scalar ≤
      (queryFamilyTagWithWork target N P F exponent H Q passes copies pass copy scalar).2 := by
  let p := (queryFinOfNatWithWork (passes + 1) pass (Nat.succ_pos _)).1
  let c := (queryFinOfNatWithWork (copies + 1) copy (Nat.succ_pos _)).1
  have hp := binaryNaturalDivAllocation_le_work pass (passes + 1)
  have hc := binaryNaturalDivAllocation_le_work copy (copies + 1)
  have hs := physicalScalarCodeAllocation_le_work scalar
  have hcp := naturalPairWithWork_lower c.val (physicalScalarCodeWithWork scalar).1
  have hpp := naturalPairWithWork_lower p.val (naturalPairWithWork c.val (physicalScalarCodeWithWork scalar).1).1
  unfold queryFamilyTagAllocation queryFamilyTagWithWork physicalFamilyCodeWithWork
  dsimp only
  dsimp only [p, c, queryFinOfNatWithWork] at hcp hpp ⊢
  omega

def queryFamilyGroupReadHeap (node : PhysicalInternalNode M J) (time : Fin R) (key : GroupScalarKey M F Q) :
    Heap (queryFamilyGroupRead target N P F exponent H Q passes copies pass copy node time key) :=
  (queryPhysicalScalarGroupReadHeap M J N target.length exponent F Q R (localOnlineMassBound M P H) node time key).mapKeysWithWork
    _ (queryFamilyTagAllocation target N P F exponent H Q passes copies pass copy)
    (queryFamilyTagAllocation_le_work target N P F exponent H Q passes copies pass copy)

def queryFamilyOnlineReadHeap (node : PhysicalInternalNode M J) (time : Fin R)
    (key : ℕ × TargetInterval target.length) (range : ℕ) :
    Heap (queryFamilyOnlineRead target N P F exponent H Q passes copies pass copy node time key range) :=
  (queryPhysicalScalarOnlineReadHeap M J N target.length exponent F Q R (localOnlineMassBound M P H) node time key range).mapKeysWithWork
    _ (queryFamilyTagAllocation target N P F exponent H Q passes copies pass copy)
    (queryFamilyTagAllocation_le_work target N P F exponent H Q passes copies pass copy)

end Family
end EditApproximation

end OAI
