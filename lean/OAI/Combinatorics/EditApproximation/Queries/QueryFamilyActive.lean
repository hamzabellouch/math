import OAI.Combinatorics.EditApproximation.Queries.QueryFamilyRefinement
import OAI.Combinatorics.EditApproximation.Queries.QueryBoundedBody
import OAI.Combinatorics.EditApproximation.Refinement.PhysicalRandomBoundedQuery

namespace OAI

/-! Positive internal refinement steps expose exactly the independent
scalar family and smaller physical table requests of the reference body. -/

namespace EditApproximation

section Active
variable {α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R]
  (source target : List α) (N P F exponent H Q eM eF : ℕ)
  (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (tau a eta kappa delta : BinaryFraction) (T S passes copies : ℕ)
  (request : PhysicalTableRequest M J target.length)
  (hindex : T < request.index) (hbelow : request.node.1.val < J)

include hindex in
omit [DecidableEq α] [NeZero M] in
private theorem active_request_eq :
    PhysicalTableRequest.refinement request.pass request.copy request.node T (request.index - T)
      request.state = request := by
  have hi : T + (request.index - T) = request.index := by omega
  unfold PhysicalTableRequest.refinement
  rw [hi]

def queryFamilyActive :
    BitQuery (Sum (PhysicalFamilyScalarKey (M := M) (J := J) (R := R)
      target N P F exponent H Q passes copies)
      {child : PhysicalTableRequest M J target.length //
        child.combinedRank T S < request.combinedRank T S}) BinaryFraction :=
  BitQuery.mapKeysWithWork
    (fun key => (Sum.map id (fun child => ⟨child.val, by
      simpa only [active_request_eq (target := target) (T := T) (request := request) (hindex := hindex)] using child.property⟩) key, 1))
    (queryFamilyRefinement (R := R) source target N P F exponent H Q eM eF hP hM hF tau a eta kappa delta
      passes copies request.pass request.copy T S (request.index - T) (Nat.sub_pos_of_lt hindex)
      request.node hbelow (Fin.ofNat R (request.index - T - 1)) request.state)

theorem queryFamilyActive_refines (factor : ℕ → ℚ) (multiplier : ℕ → ℕ)
    (initial : PhysicalEntry M J target.length → ℕ)
    (ha : a.value = refinementFactor (factor request.pass) F)
    (hlong : ¬ (physicalSourceInterval source.length request.node).hi -
      (physicalSourceInterval source.length request.node).lo ≤ 1) :
    BitQuery.Refines (fun word value => word.value = value)
      (queryFamilyActive (R := R) source target N P F exponent H Q eM eF hP hM hF tau a eta kappa delta
        T S passes copies request hindex hbelow)
      (physicalRandomGlobalQuery (R := R) source target N P F exponent H Q T S copies factor multiplier
        tau.value eta.value kappa.value delta.value
        (physicalFamilyGroupRead target N P F exponent H Q passes copies)
        (physicalFamilyOnlineRead target N P F exponent H Q passes copies) initial request) := by
  unfold queryFamilyActive physicalRandomGlobalQuery
  rw [dite_eq_left ⟨hindex, hbelow, hlong⟩]
  apply BitQuery.Refines.mapKeysWithWork _ _ (fun _ => rfl)
  simpa only [ha] using queryFamilyRefinement_refines (R := R) source target N P F exponent H Q eM eF
    hP hM hF tau a eta kappa delta passes copies request.pass request.copy T S
    (request.index - T) (Nat.sub_pos_of_lt hindex) request.node hbelow
    (Fin.ofNat R (request.index - T - 1)) request.state

end Active

section Bounded
variable {α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R]
  (source target : List α) (N P F exponent H Q eM eF : ℕ)
  (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (tau a eta kappa delta : BinaryFraction) (T S passes copies : ℕ)
  (parent : {r : PhysicalTableRequest M J target.length // r.Bounded (passes + 1) copies T S})
  (hindex : T < parent.val.index) (hbelow : parent.val.node.1.val < J)

def queryFamilyBoundedActive :
    BitQuery (Sum (PhysicalFamilyScalarKey (M := M) (J := J) (R := R)
      target N P F exponent H Q passes copies)
      {child : {r : PhysicalTableRequest M J target.length // r.Bounded (passes + 1) copies T S} //
        child.val.combinedRank T S < parent.val.combinedRank T S}) BinaryFraction :=
  queryRestrictPhysicalBody (passes + 1) copies T S parent
    (queryFamilyActive (R := R) source target N P F exponent H Q eM eF hP hM hF tau a eta kappa delta
      T S passes copies parent.val hindex hbelow)

theorem queryFamilyBoundedActive_refines (factor : ℕ → ℚ) (multiplier : ℕ → ℕ)
    (initial : PhysicalEntry M J target.length → ℕ)
    (ha : a.value = refinementFactor (factor parent.val.pass) F)
    (hlong : ¬ (physicalSourceInterval source.length parent.val.node).hi -
      (physicalSourceInterval source.length parent.val.node).lo ≤ 1) :
    BitQuery.Refines (fun word value => word.value = value)
      (queryFamilyBoundedActive (R := R) source target N P F exponent H Q eM eF hP hM hF tau a eta kappa delta
        T S passes copies parent hindex hbelow)
      (physicalRandomBoundedQuery (R := R) source target N P F exponent H Q T S (passes + 1) copies factor multiplier
        tau.value eta.value kappa.value delta.value
        (physicalFamilyGroupRead target N P F exponent H Q passes copies)
        (physicalFamilyOnlineRead target N P F exponent H Q passes copies) initial parent) := by
  apply queryRestrictPhysicalBody_refines
  exact queryFamilyActive_refines (R := R) source target N P F exponent H Q eM eF hP hM hF
    tau a eta kappa delta T S passes copies parent.val hindex hbelow factor multiplier initial ha hlong

end Bounded
end EditApproximation

end OAI
