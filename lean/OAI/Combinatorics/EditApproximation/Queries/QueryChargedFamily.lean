import OAI.Combinatorics.EditApproximation.Queries.QueryFamilyActive
import OAI.Combinatorics.EditApproximation.Queries.QueryChargedWarmup
import OAI.Combinatorics.EditApproximation.Geometry.ChargedRandomGlobalQuery
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! All physical table branches run Boolean arithmetic and issue
address-charged adaptive requests.  Coarse entries are supplied by the
separately executed coarse initializer. -/

namespace EditApproximation

section Family
variable {M J R passes copies T S : ℕ} [NeZero M] [NeZero R]
  (source target : List ℕ) (N P F exponent H Q eM eF : ℕ)
  (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (A a : ℕ → BinaryFraction) (tau eta kappa delta : BinaryFraction) (multiplier : ℕ → ℕ)
  (occurrence : BinaryMemo PositionCounts) (symbolBits positionBits : ℕ)



def queryChargedFamilyTable
    (parent : {r : PhysicalTableRequest M J target.length // r.Bounded (passes + 1) copies T S}) :
    BitQuery (ChargedFamilyQueryKey (R := R) target N P F exponent H Q (.inr parent)) BinaryFraction :=
  let index := wordLEWithWork parent.val.index.bits T.bits
  .charge (index.2 + 1)
    (if hi : index.1 = true then
      BitQuery.mapKeysWithWork (fun key => (Sum.inr key, 1))
        (queryChargedWarmup source target N P F (A parent.val.pass) (a parent.val.pass) multiplier
          parent occurrence symbolBits positionBits)
    else let depth := binaryNaturalCompareWithWork parent.val.node.1.val J
      .charge (depth.2 + 1)
        (if hb : depth.1 = .lt then
          let interval := physicalSourceInterval source.length parent.val.node
          let length := saturatingSubtractWithWork interval.hi interval.lo
          let short := wordLEWithWork length.1 [true]
          .charge (length.2 + short.2 + 1)
            (if short.1 then
              BitQuery.mapKeysWithWork (fun key => (Sum.inr key, 1))
                (queryPhysicalInitial source target N P F (A parent.val.pass) (a parent.val.pass)
                  multiplier parent occurrence symbolBits positionBits parent.val.state)
            else BitQuery.mapKeysWithWork
              (fun key => (Sum.map id (fun child =>
                ⟨Sum.inr child.val, ChargedPhysicalRequest.table_rank_lt parent child.val child.property⟩)
                key, 1))
              (queryFamilyBoundedActive (R := R) source target N P F exponent H Q eM eF hP hM hF
                tau (a parent.val.pass) eta kappa delta T S passes copies parent
                (Nat.lt_of_not_ge (fun h => hi ((queryNaturalLEWithWork_value parent.val.index T).mpr h)))
                ((binaryNaturalCompareWithWork_lt _ _).mp hb)))
        else BitQuery.mapKeysWithWork (fun key => (Sum.inr key, 1))
          (queryPhysicalInitial source target N P F (A parent.val.pass) (a parent.val.pass)
            multiplier parent occurrence symbolBits positionBits parent.val.state)))

theorem queryChargedFamilyTable_refines
    (ha : ∀ pass, pass ≤ passes → (a pass).value = refinementFactor (A pass).value F)
    (hs : ∀ z ∈ source, z < 2 ^ symbolBits) (ht : ∀ z ∈ target, z < 2 ^ symbolBits)
    (hp : target.length ≤ 2 ^ positionBits)
    (htable : occurrence = occurrenceBuild symbolBits positionBits target.zipIdx)
    (initial : PhysicalEntry M J target.length → ℕ)
    (parent : {r : PhysicalTableRequest M J target.length // r.Bounded (passes + 1) copies T S}) :
    BitQuery.Refines (fun word value => word.value = value)
      (queryChargedFamilyTable (R := R) source target N P F exponent H Q eM eF hP hM hF
        A a tau eta kappa delta multiplier occurrence symbolBits positionBits parent)
      (chargedRandomGlobalQuery (R := R) source target N P F exponent H Q T S (passes + 1) copies
        (fun pass => (A pass).value) multiplier tau.value eta.value kappa.value delta.value
        (physicalFamilyGroupRead target N P F exponent H Q passes copies)
        (physicalFamilyOnlineRead target N P F exponent H Q passes copies) initial (.inr parent)) := by
  have hinit := queryPhysicalInitial_refines source target N P F (A parent.val.pass)
    (a parent.val.pass) multiplier parent occurrence symbolBits positionBits parent.val.state hP
    (ha parent.val.pass (by have := parent.property.1; omega)) hs ht hp htable
  unfold queryChargedFamilyTable chargedRandomGlobalQuery
  dsimp only
  apply BitQuery.Refines.charge
  by_cases hi : parent.val.index ≤ T
  · rw [ite_eq_left hi, dite_eq_left ((queryNaturalLEWithWork_value parent.val.index T).mpr hi)]
    apply BitQuery.Refines.mapKeysWithWork _ _ (fun _ => rfl)
    exact queryChargedWarmup_refines source target N P F (A parent.val.pass) (a parent.val.pass)
      multiplier parent occurrence symbolBits positionBits (fun pass => (A pass).value) rfl hP
      (ha parent.val.pass (by have := parent.property.1; omega)) hs ht hp htable
  · rw [ite_eq_right hi, dite_eq_right (fun h => hi ((queryNaturalLEWithWork_value parent.val.index T).mp h))]
    apply BitQuery.Refines.charge
    by_cases hb : parent.val.node.1.val < J
    · rw [ite_eq_left hb, dite_eq_left ((binaryNaturalCompareWithWork_lt _ _).mpr hb)]
      apply BitQuery.Refines.charge
      have hshort : (wordLEWithWork
          (saturatingSubtractWithWork (physicalSourceInterval source.length parent.val.node).hi
            (physicalSourceInterval source.length parent.val.node).lo).1 [true]).1 = true ↔
          (physicalSourceInterval source.length parent.val.node).hi -
            (physicalSourceInterval source.length parent.val.node).lo ≤ 1 := by
        rw [wordLEWithWork_value, saturatingSubtractWithWork_value]
        rfl
      by_cases hw : (physicalSourceInterval source.length parent.val.node).hi -
          (physicalSourceInterval source.length parent.val.node).lo ≤ 1
      · rw [ite_eq_left hw, ite_eq_left (hshort.mpr hw)]
        exact hinit.mapKeysWithWork _ _ (fun _ => rfl)
      · rw [ite_eq_right hw, ite_eq_right (fun h => hw (hshort.mp h))]
        apply BitQuery.Refines.mapKeysWithWork _ _ (fun _ => rfl)
        exact queryFamilyBoundedActive_refines (R := R) source target N P F exponent H Q eM eF
          hP hM hF tau (a parent.val.pass) eta kappa delta T S passes copies parent
          (Nat.lt_of_not_ge hi) hb (fun pass => (A pass).value) multiplier initial (ha parent.val.pass (by have := parent.property.1; omega)) hw
    · rw [ite_eq_right hb, dite_eq_right (fun h => hb ((binaryNaturalCompareWithWork_lt _ _).mp h))]
      exact hinit.mapKeysWithWork _ _ (fun _ => rfl)

def queryChargedFamilyGlobal
    (coarse : PhysicalEntry M J target.length → BinaryFraction × ℕ)
    (request : ChargedPhysicalRequest M J target.length (passes + 1) copies T S) :
    BitQuery (ChargedFamilyQueryKey (R := R) target N P F exponent H Q request) BinaryFraction :=
  match request with
  | .inl entry => BitQuery.compute (coarse entry)
  | .inr parent => queryChargedFamilyTable (R := R) source target N P F exponent H Q eM eF hP hM hF
      A a tau eta kappa delta multiplier occurrence symbolBits positionBits parent

theorem queryChargedFamilyGlobal_refines
    (ha : ∀ pass, pass ≤ passes → (a pass).value = refinementFactor (A pass).value F)
    (hs : ∀ z ∈ source, z < 2 ^ symbolBits) (ht : ∀ z ∈ target, z < 2 ^ symbolBits)
    (hp : target.length ≤ 2 ^ positionBits)
    (htable : occurrence = occurrenceBuild symbolBits positionBits target.zipIdx)
    (coarse : PhysicalEntry M J target.length → BinaryFraction × ℕ)
    (initial : PhysicalEntry M J target.length → ℕ)
    (hc : ∀ entry, (coarse entry).1.value = initial entry)
    (request : ChargedPhysicalRequest M J target.length (passes + 1) copies T S) :
    BitQuery.Refines (fun word value => word.value = value)
      (queryChargedFamilyGlobal (R := R) source target N P F exponent H Q eM eF hP hM hF
        A a tau eta kappa delta multiplier occurrence symbolBits positionBits coarse request)
      (chargedRandomGlobalQuery (R := R) source target N P F exponent H Q T S (passes + 1) copies
        (fun pass => (A pass).value) multiplier tau.value eta.value kappa.value delta.value
        (physicalFamilyGroupRead target N P F exponent H Q passes copies)
        (physicalFamilyOnlineRead target N P F exponent H Q passes copies) initial request) := by
  cases request with
  | inl entry => exact .charge _ (.done (hc entry))
  | inr parent =>
    exact queryChargedFamilyTable_refines (R := R) source target N P F exponent H Q eM eF hP hM hF
      A a tau eta kappa delta multiplier occurrence symbolBits positionBits ha hs ht hp htable initial parent

end Family
end EditApproximation

end OAI
