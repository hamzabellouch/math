import OAI.Combinatorics.EditApproximation.Refinement.PhysicalRandomBoundedCost
import OAI.Combinatorics.EditApproximation.Geometry.ChargedRandomGlobalQuery
import OAI.Combinatorics.EditApproximation.Geometry.ChargedIndexCost
import OAI.Combinatorics.EditApproximation.Refinement.PhysicalRandomRankCost

namespace OAI

namespace EditApproximation

section Cost

variable {σ α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R]
  (source target : List α) (N P F exponent H Q T S passes copies : ℕ)
  (factor : ℕ → ℚ) (multiplier : ℕ → ℕ) (tau eta kappa delta : ℚ)
  (readGroup : ℕ → ℕ → PhysicalInternalNode M J → Fin R → GroupScalarKey M F Q → FiniteQuery σ)
  (readInteger : ℕ → ℕ → PhysicalInternalNode M J → Fin R →
    (ℕ × TargetInterval target.length) → ℕ → FiniteQuery σ)
  (initial : PhysicalEntry M J target.length → ℕ)
  (sourceAnswer : σ → ℚ) (answer : PhysicalTableRequest M J target.length → ℚ)
  (sourceWeight : σ → ℕ) (coarse : ℕ) (weight : PhysicalTableRequest M J target.length → ℕ)

 theorem physicalRandomGlobalQuery_refinement_cost
    (request : PhysicalTableRequest M J target.length)
    (hindex : T < request.index) (hbelow : request.node.1.val < J)
    (hshort : ¬ (physicalSourceInterval source.length request.node).hi -
      (physicalSourceInterval source.length request.node).lo ≤ 1) :
    (physicalRandomGlobalQuery source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta readGroup readInteger initial request).cost
      (Sum.elim sourceAnswer (fun child => answer child.val))
      (Sum.elim sourceWeight (fun child => weight child.val)) =
    (physicalRandomDataRequestQuery source target N P F exponent H Q tau
      (refinementFactor (factor request.pass) F) eta kappa delta request.pass request.copy T S
      (request.index - T) (Nat.sub_pos_of_lt hindex) request.node hbelow
      (readGroup request.pass request.copy ⟨request.node, hbelow⟩ (Fin.ofNat R (request.index - T - 1)))
      (readInteger request.pass request.copy ⟨request.node, hbelow⟩ (Fin.ofNat R (request.index - T - 1)))
      request.state).cost (Sum.elim sourceAnswer (fun child => answer child.val))
        (Sum.elim sourceWeight (fun child => weight child.val)) := by
  unfold physicalRandomGlobalQuery
  rw [dite_eq_left ⟨hindex, hbelow, hshort⟩, FiniteQuery.mapKeys_cost]
  congr 1 <;> (funext key; cases key <;> rfl)

 theorem chargedRandomGlobalQuery_refinement_cost
    (parent : {r : PhysicalTableRequest M J target.length // r.Bounded passes copies T S})
    (hindex : T < parent.val.index) (hbelow : parent.val.node.1.val < J)
    (hshort : ¬ (physicalSourceInterval source.length parent.val.node).hi -
      (physicalSourceInterval source.length parent.val.node).lo ≤ 1) :
    (chargedRandomGlobalQuery source target N P F exponent H Q T S passes copies factor multiplier
      tau eta kappa delta readGroup readInteger initial (Sum.inr parent)).cost
      (Sum.elim sourceAnswer (fun child => Sum.elim (fun entry => (initial entry : ℚ))
        (fun r => answer r.val) child.val))
      (Sum.elim sourceWeight (fun child => chargedTableWeight coarse weight child.val)) =
    (physicalRandomDataRequestQuery source target N P F exponent H Q tau
      (refinementFactor (factor parent.val.pass) F) eta kappa delta parent.val.pass parent.val.copy T S
      (parent.val.index - T) (Nat.sub_pos_of_lt hindex) parent.val.node hbelow
      (readGroup parent.val.pass parent.val.copy ⟨parent.val.node, hbelow⟩
        (Fin.ofNat R (parent.val.index - T - 1)))
      (readInteger parent.val.pass parent.val.copy ⟨parent.val.node, hbelow⟩
        (Fin.ofNat R (parent.val.index - T - 1))) parent.val.state).cost
      (Sum.elim sourceAnswer (fun child => answer child.val))
      (Sum.elim sourceWeight (fun child => weight child.val)) := by
  unfold chargedRandomGlobalQuery
  dsimp only
  rw [ite_eq_right (Nat.not_le.mpr hindex), ite_eq_left hbelow, ite_eq_right hshort, FiniteQuery.mapKeys_cost]
  have hcost := physicalRandomBoundedQuery_cost source target N P F exponent H Q T S passes copies
    factor multiplier tau eta kappa delta readGroup readInteger initial sourceAnswer answer
    sourceWeight weight parent
  have heq : (physicalRandomBoundedQuery source target N P F exponent H Q T S passes copies
      factor multiplier tau eta kappa delta readGroup readInteger initial parent).cost
      (Sum.elim sourceAnswer (fun child => answer child.val.val))
      (Sum.elim sourceWeight (fun child => weight child.val.val)) = _ := hcost
  calc
    _ = (physicalRandomBoundedQuery source target N P F exponent H Q T S passes copies
        factor multiplier tau eta kappa delta readGroup readInteger initial parent).cost
        (Sum.elim sourceAnswer (fun child => answer child.val.val))
        (Sum.elim sourceWeight (fun child => weight child.val.val)) := by
      congr 1 <;> (funext key; cases key <;> rfl)
    _ = _ := heq.trans (physicalRandomGlobalQuery_refinement_cost source target N P F exponent H Q T S
      copies factor multiplier tau eta kappa delta readGroup readInteger initial sourceAnswer answer
      sourceWeight weight parent.val hindex hbelow hshort)

end Cost

end EditApproximation

end OAI
