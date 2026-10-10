import OAI.Combinatorics.EditApproximation.Geometry.ChargedGlobalQuery
import OAI.Combinatorics.EditApproximation.Refinement.PhysicalQueryProgress

namespace OAI

/-! Exact weighted-cost transport for the full internal refinement body.
In this branch every request is an ordinary table request: parent initial,
child mass, child initial, old history or a current physical child. -/

namespace EditApproximation

namespace FiniteQuery

theorem cost_congr_weights {ι : Type*} (oracle : ι → ℚ) (program : FiniteQuery ι)
    (left right : ι → ℕ) (heq : ∀ key ∈ program.keys oracle, left key = right key) :
    program.cost oracle left = program.cost oracle right := by
  rw [cost_eq_sum, cost_eq_sum]
  congr 1
  exact List.map_congr_left heq

end FiniteQuery

def chargedTableWeight {M J ny passes copies T S : ℕ}
    (coarse : ℕ) (weight : PhysicalTableRequest M J ny → ℕ) :
    ChargedPhysicalRequest M J ny passes copies T S → ℕ
  | .inl _ => coarse
  | .inr request => weight request.val

section Costs

variable {α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero R]
  (source target : List α) (N P F exponent H Q T S passes copies : ℕ)
  (factor : ℕ → ℚ) (multiplier : ℕ → ℕ) (tau eta kappa delta : ℚ)
  (group : ℕ → ℕ → PhysicalInternalNode M J → Fin R → CellGroupDraws M F Q)
  (integer : ℕ → ℕ → PhysicalInternalNode M J → Fin R → ℕ → TargetInterval target.length → ℕ)
  (initial : PhysicalEntry M J target.length → ℕ)

theorem physicalBoundedQuery_cost
    (request : {r : PhysicalTableRequest M J target.length // r.Bounded passes copies T S})
    (weight : PhysicalTableRequest M J target.length → ℕ) :
    (physicalBoundedQuery source target N P F exponent H Q T S passes copies factor multiplier
      tau eta kappa delta group integer initial request).cost
      (fun child => localRequestValue source target N P F exponent H Q T S copies factor multiplier
        tau eta kappa delta group integer initial child.val.val) (fun child => weight child.val.val) =
    (physicalGlobalQuery source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta group integer initial request.val).cost
      (fun child => localRequestValue source target N P F exponent H Q T S copies factor multiplier
        tau eta kappa delta group integer initial child.val) (fun child => weight child.val) := by
  unfold physicalBoundedQuery
  exact restrictRankedProgram_cost _ _ _ _ weight request
    (physicalGlobalQuery_keys_bounded source target N P F exponent H Q T S passes copies factor multiplier
      tau eta kappa delta group integer initial request.val request.property _)

theorem physicalGlobalQuery_refinement_cost (request : PhysicalTableRequest M J target.length)
    (hindex : T < request.index) (hbelow : request.node.1.val < J)
    (hshort : ¬ (physicalSourceInterval source.length request.node).hi -
      (physicalSourceInterval source.length request.node).lo ≤ 1)
    (values : PhysicalTableRequest M J target.length → ℚ)
    (weight : PhysicalTableRequest M J target.length → ℕ) :
    (physicalGlobalQuery source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta group integer initial request).cost
      (fun child => values child.val) (fun child => weight child.val) =
    (physicalRefinementDataRequestQuery source target N P F exponent H Q tau
      (refinementFactor (factor request.pass) F) eta kappa delta request.pass request.copy T S
      (request.index - T) (Nat.sub_pos_of_lt hindex) request.node hbelow
      (group request.pass request.copy ⟨request.node, hbelow⟩ (Fin.ofNat R (request.index - T - 1)))
      (integer request.pass request.copy ⟨request.node, hbelow⟩ (Fin.ofNat R (request.index - T - 1)))
      request.state).cost (fun child => values child.val) (fun child => weight child.val) := by
  unfold physicalGlobalQuery
  dsimp only
  erw [dite_eq_right (Nat.not_le.mpr hindex), dite_eq_left hbelow, dite_eq_right hshort]
  rw [FiniteQuery.mapKeys_cost]
  rfl


theorem chargedGlobalQuery_refinement_cost
    (parent : {r : PhysicalTableRequest M J target.length // r.Bounded passes copies T S})
    (hindex : T < parent.val.index) (hbelow : parent.val.node.1.val < J)
    (hshort : ¬ (physicalSourceInterval source.length parent.val.node).hi -
      (physicalSourceInterval source.length parent.val.node).lo ≤ 1)
    (coarse : ℕ) (weight : PhysicalTableRequest M J target.length → ℕ) :
    (chargedGlobalQuery source target N P F exponent H Q T S passes copies factor multiplier
      tau eta kappa delta group integer initial (Sum.inr parent)).cost
      (fun child => chargedRequestValue source target N P F exponent H Q T S passes copies
        factor multiplier tau eta kappa delta group integer initial child.val)
      (fun child => chargedTableWeight coarse weight child.val) =
    (physicalRefinementDataRequestQuery source target N P F exponent H Q tau
      (refinementFactor (factor parent.val.pass) F) eta kappa delta parent.val.pass parent.val.copy T S
      (parent.val.index - T) (Nat.sub_pos_of_lt hindex) parent.val.node hbelow
      (group parent.val.pass parent.val.copy ⟨parent.val.node, hbelow⟩ (Fin.ofNat R (parent.val.index - T - 1)))
      (integer parent.val.pass parent.val.copy ⟨parent.val.node, hbelow⟩ (Fin.ofNat R (parent.val.index - T - 1)))
      parent.val.state).cost
      (fun child => localRequestValue source target N P F exponent H Q T S copies factor multiplier
        tau eta kappa delta group integer initial child.val) (fun child => weight child.val) := by
  unfold chargedGlobalQuery
  dsimp only
  rw [ite_eq_right (Nat.not_le.mpr hindex), ite_eq_left hbelow, ite_eq_right hshort,
    FiniteQuery.mapKeys_cost]
  simp only [Function.comp_def, chargedRequestValue, chargedTableWeight]
  rw [physicalBoundedQuery_cost source target N P F exponent H Q T S passes copies factor multiplier
    tau eta kappa delta group integer initial parent weight]
  exact physicalGlobalQuery_refinement_cost source target N P F exponent H Q T S copies factor multiplier
    tau eta kappa delta group integer initial parent.val hindex hbelow hshort _ weight

end Costs

end EditApproximation

end OAI
