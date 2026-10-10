import OAI.Combinatorics.EditApproximation.Refinement.ComputedFamilyMemoCode
import OAI.Combinatorics.EditApproximation.Geometry.ParameterConstruction
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Address generation is charged separately from binary trie traversal.
The loops visit only coordinates in a key, never the ambient key space. -/
namespace EditApproximation



 @[simp] theorem naturalPairWithWork_value (a b : ℕ) :
    (naturalPairWithWork a b).1 = Nat.pair a b := by
  unfold naturalPairWithWork Nat.pair
  split_ifs <;> rfl

 theorem naturalPairWithWork_cost (a b : ℕ) : (naturalPairWithWork a b).2 ≤ 5 := by
  unfold naturalPairWithWork
  split_ifs <;> dsimp only <;> decide



 @[simp] theorem treeLayerCodeWithWork_value (M d : ℕ) (path : TreeLayer M d) :
    (treeLayerCodeWithWork M d path).1 = treeLayerCode M d path := by
  induction d with
  | zero => rfl
  | succ d ih => simp only [treeLayerCodeWithWork, treeLayerCode, ih]

 theorem treeLayerCodeWithWork_cost (M d : ℕ) (path : TreeLayer M d) :
    (treeLayerCodeWithWork M d path).2 = 3 * d + 1 := by
  induction d with
  | zero => rfl
  | succ d ih => simp only [treeLayerCodeWithWork, ih]; omega



 @[simp] theorem physicalNodeCodeWithWork_value {M J : ℕ} (node : PhysicalNode M J) :
    (physicalNodeCodeWithWork node).1 = physicalNodeCode node := by
  simp only [physicalNodeCodeWithWork, treeLayerCodeWithWork_value,
    parameterPowerWithWork_spec, physicalNodeCode]

 theorem physicalNodeCodeWithWork_cost {M J : ℕ} (node : PhysicalNode M J) :
    (physicalNodeCodeWithWork node).2 ≤ 5 * J + 5 := by
  have h := node.1.isLt
  simp only [physicalNodeCodeWithWork, treeLayerCodeWithWork_cost, parameterPowerWithWork_spec]
  omega



 @[simp] theorem physicalEntryCodeWithWork_value {M J n : ℕ} (entry : PhysicalEntry M J n) :
    (physicalEntryCodeWithWork entry).1 = physicalEntryCode entry := by
  simp only [physicalEntryCodeWithWork, physicalNodeCodeWithWork_value,
    physicalEntryCode, childInputCode, Fin.val_zero, zero_add, one_mul, pow_two]

 theorem physicalEntryCodeWithWork_cost {M J n : ℕ} (entry : PhysicalEntry M J n) :
    (physicalEntryCodeWithWork entry).2 ≤ 5 * J + 13 := by
  have h := physicalNodeCodeWithWork_cost entry.1
  change (physicalNodeCodeWithWork entry.1).2 + 8 ≤ _
  omega



 @[simp] theorem physicalTableCodeWithWork_value {M J n : ℕ} (copies T S : ℕ)
    (request : PhysicalTableRequest M J n) :
    (physicalTableCodeWithWork copies T S request).1 = PhysicalTableRequest.code copies T S request := by
  simp only [physicalTableCodeWithWork, physicalEntryCodeWithWork_value,
    parameterPowerWithWork_spec, PhysicalTableRequest.code, PhysicalTableRequest.entryCapacity, pow_two]

 theorem physicalTableCodeWithWork_cost {M J n : ℕ} (copies T S : ℕ)
    (request : PhysicalTableRequest M J n) :
    (physicalTableCodeWithWork copies T S request).2 ≤ 7 * J + 29 := by
  have he := physicalEntryCodeWithWork_cost (request.node, request.state)
  simp only [physicalTableCodeWithWork, parameterPowerWithWork_spec]
  omega



 @[simp] theorem chargedPhysicalCodeWithWork_value {M J n passes copies T S : ℕ}
    (request : ChargedPhysicalRequest M J n passes copies T S) :
    (chargedPhysicalCodeWithWork request).1 = request.code := by
  cases request <;> simp only [chargedPhysicalCodeWithWork, ChargedPhysicalRequest.code,
    physicalEntryCodeWithWork_value, physicalTableCodeWithWork_value]

 theorem chargedPhysicalCodeWithWork_cost {M J n passes copies T S : ℕ}
    (request : ChargedPhysicalRequest M J n passes copies T S) :
    (chargedPhysicalCodeWithWork request).2 ≤ 7 * J + 32 := by
  cases request with
  | inl entry => have h := physicalEntryCodeWithWork_cost entry
                 change (physicalEntryCodeWithWork entry).2 + 2 ≤ _
                 omega
  | inr request => have h := physicalTableCodeWithWork_cost copies T S request.val
                   change (physicalTableCodeWithWork copies T S request.val).2 + 3 ≤ _
                   omega



 @[simp] theorem physicalScalarCodeWithWork_value {M J N n exponent F Q R B : ℕ}
    (key : PhysicalScalarKey M J N n exponent F Q R B) :
    (physicalScalarCodeWithWork key).1 = physicalScalarCode key := by
  rcases key with ⟨online | group, index⟩ <;>
    simp only [physicalScalarCodeWithWork, naturalPairWithWork_value,
      physicalEntryCodeWithWork_value, physicalNodeCodeWithWork_value, physicalScalarCode]

 theorem physicalScalarCodeWithWork_cost {M J N n exponent F Q R B : ℕ}
    (key : PhysicalScalarKey M J N n exponent F Q R B) :
    (physicalScalarCodeWithWork key).2 ≤ 5 * J + 40 := by
  rcases key with ⟨online | group, index⟩
  · have hn := physicalEntryCodeWithWork_cost (online.1.1.val, online.1.2.2)
    have ha := naturalPairWithWork_cost online.2.val.val index.val
    have hb := naturalPairWithWork_cost online.1.2.1.val
      (naturalPairWithWork online.2.val.val index.val).1
    have hc := naturalPairWithWork_cost (physicalEntryCodeWithWork (online.1.1.val, online.1.2.2)).1
      (naturalPairWithWork online.1.2.1.val (naturalPairWithWork online.2.val.val index.val).1).1
    dsimp only [physicalScalarCodeWithWork]
    omega
  · have hn := physicalNodeCodeWithWork_cost group.1.val
    have ha := naturalPairWithWork_cost index.2.1.val index.2.2.val
    have hb := naturalPairWithWork_cost index.1.val (naturalPairWithWork index.2.1.val index.2.2.val).1
    have hc := naturalPairWithWork_cost group.2.2.2.val
      (naturalPairWithWork index.1.val (naturalPairWithWork index.2.1.val index.2.2.val).1).1
    have hd := naturalPairWithWork_cost group.2.2.1.val
      (naturalPairWithWork group.2.2.2.val
        (naturalPairWithWork index.1.val (naturalPairWithWork index.2.1.val index.2.2.val).1).1).1
    have he := naturalPairWithWork_cost group.2.1.val
      (naturalPairWithWork group.2.2.1.val
        (naturalPairWithWork group.2.2.2.val
          (naturalPairWithWork index.1.val (naturalPairWithWork index.2.1.val index.2.2.val).1).1).1).1
    have hf := naturalPairWithWork_cost (physicalNodeCodeWithWork group.1.val).1
      (naturalPairWithWork group.2.1.val
        (naturalPairWithWork group.2.2.1.val
          (naturalPairWithWork group.2.2.2.val
            (naturalPairWithWork index.1.val (naturalPairWithWork index.2.1.val index.2.2.val).1).1).1).1).1
    dsimp only [physicalScalarCodeWithWork]
    omega

section Family
variable {α : Type*} {M J R : ℕ} (target : List α) (N P F exponent H Q passes copies : ℕ)



 @[simp] theorem physicalFamilyCodeWithWork_value
    (key : PhysicalFamilyScalarKey (M := M) (J := J) (R := R)
      target N P F exponent H Q passes copies) :
    (physicalFamilyCodeWithWork target N P F exponent H Q passes copies key).1 =
      physicalFamilyCode target N P F exponent H Q passes copies key := by
  simp only [physicalFamilyCodeWithWork, physicalScalarCodeWithWork_value,
    naturalPairWithWork_value, physicalFamilyCode]

 theorem physicalFamilyCodeWithWork_cost
    (key : PhysicalFamilyScalarKey (M := M) (J := J) (R := R)
      target N P F exponent H Q passes copies) :
    (physicalFamilyCodeWithWork target N P F exponent H Q passes copies key).2 ≤ 5 * J + 52 := by
  have hs := physicalScalarCodeWithWork_cost key.2.2
  have hc := naturalPairWithWork_cost key.2.1.val (physicalScalarCodeWithWork key.2.2).1
  have hp := naturalPairWithWork_cost key.1.val
    (naturalPairWithWork key.2.1.val (physicalScalarCodeWithWork key.2.2).1).1
  dsimp only [physicalFamilyCodeWithWork]
  omega
end Family



 @[simp] theorem computedFamilyMemoCodeWithWork_value (source target : List ℕ) (N R : ℕ)
    (key : Sum (ComputedFamilyScalarKey source target N R) (ComputedFamilyTableKey source target N)) :
    (computedFamilyMemoCodeWithWork source target N R key).1 = computedFamilyMemoCode source target N R key := by
  cases key <;> simp only [computedFamilyMemoCodeWithWork, computedFamilyMemoCode,
    SourceRanked.keyCode, physicalFamilyCodeWithWork_value, chargedPhysicalCodeWithWork_value]

 theorem computedFamilyMemoCodeWithWork_cost (source target : List ℕ) (N R : ℕ)
    (key : Sum (ComputedFamilyScalarKey source target N R) (ComputedFamilyTableKey source target N)) :
    (computedFamilyMemoCodeWithWork source target N R key).2 ≤
      7 * intervalTreeDepth (integerParameters N).M source.length + 60 := by
  cases key with
  | inl key =>
    have h := physicalFamilyCodeWithWork_cost target N (integerParameters N).P (inputSmallLog N)
      (40 * smallLogExponent N) (inputHeight N) (inputSmallLog N ^ 80)
      (computedSeedPassCount N) (inputHeight N ^ 2) key
    change (physicalFamilyCodeWithWork target N (integerParameters N).P (inputSmallLog N)
      (40 * smallLogExponent N) (inputHeight N) (inputSmallLog N ^ 80)
      (computedSeedPassCount N) (inputHeight N ^ 2) key).2 + 2 ≤ _
    omega
  | inr key =>
    have h := chargedPhysicalCodeWithWork_cost key
    change (chargedPhysicalCodeWithWork key).2 + 3 ≤ _
    omega

end EditApproximation

end OAI
