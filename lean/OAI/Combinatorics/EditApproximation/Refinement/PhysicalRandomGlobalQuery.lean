import OAI.Combinatorics.EditApproximation.Refinement.PhysicalRandomDataRequest
import OAI.Combinatorics.EditApproximation.Refinement.PhysicalGlobalValue
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Global physical table bodies with explicit random reads. Only positive
internal refinement steps request random coordinates. All other cases
use finite warmup and initial queries. -/

namespace EditApproximation

private theorem inactiveIfEq {β : Type*} (a b c : Prop) [Decidable a] [Decidable b] [Decidable c]
    (x y : β) (z : ¬ a → b → ¬ c → β) (h : ¬ (¬ a ∧ b ∧ ¬ c)) :
    (if a then x else y) =
      (if ha : a then x else if hb : b then if hc : c then y else z ha hb hc else y) := by
  by_cases ha : a
  · simp only [ite_eq_left ha, dite_eq_left ha]
  · by_cases hb : b
    · have hc : c := by
        by_contra hc
        exact h ⟨ha, hb, hc⟩
      simp only [ite_eq_right ha, dite_eq_right ha, dite_eq_left hb, dite_eq_left hc]
    · simp only [ite_eq_right ha, dite_eq_right ha, dite_eq_right hb]

section Global

variable {σ α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R]
  (source target : List α) (N P F exponent H Q T S copies : ℕ)
  (factor : ℕ → ℚ) (multiplier : ℕ → ℕ) (tau eta kappa delta : ℚ)
  (readGroup : ℕ → ℕ → PhysicalInternalNode M J → Fin R → GroupScalarKey M F Q → FiniteQuery σ)
  (readInteger : ℕ → ℕ → PhysicalInternalNode M J → Fin R →
    (ℕ × TargetInterval target.length) → ℕ → FiniteQuery σ)
  (initial : PhysicalEntry M J target.length → ℕ)





omit [NeZero M] in
 theorem physicalGlobalQuery_inactive
    (group : ℕ → ℕ → PhysicalInternalNode M J → Fin R → CellGroupDraws M F Q)
    (integer : ℕ → ℕ → PhysicalInternalNode M J → Fin R → ℕ → TargetInterval target.length → ℕ)
    (request : PhysicalTableRequest M J target.length)
    (hinactive : ¬ (T < request.index ∧ request.node.1.val < J ∧
      ¬ (physicalSourceInterval source.length request.node).hi -
        (physicalSourceInterval source.length request.node).lo ≤ 1)) :
    physicalInactiveGlobalQuery source target N P F T S copies factor multiplier initial request =
    physicalGlobalQuery source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta group integer initial request := by
  unfold physicalInactiveGlobalQuery physicalGlobalQuery
  dsimp only
  apply inactiveIfEq
  rintro ⟨hi, hb, hs⟩
  exact hinactive ⟨Nat.lt_of_not_ge hi, hb, hs⟩

 theorem physicalRandomGlobalQuery_inactive
    (group : ℕ → ℕ → PhysicalInternalNode M J → Fin R → CellGroupDraws M F Q)
    (integer : ℕ → ℕ → PhysicalInternalNode M J → Fin R → ℕ → TargetInterval target.length → ℕ)
    (request : PhysicalTableRequest M J target.length)
    (hinactive : ¬ (T < request.index ∧ request.node.1.val < J ∧
      ¬ (physicalSourceInterval source.length request.node).hi -
        (physicalSourceInterval source.length request.node).lo ≤ 1)) :
    physicalRandomGlobalQuery source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta readGroup readInteger initial request =
      FiniteQuery.mapKeys Sum.inr (physicalGlobalQuery source target N P F exponent H Q T S copies
        factor multiplier tau eta kappa delta group integer initial request) := by
  unfold physicalRandomGlobalQuery
  rw [dite_eq_right hinactive,
    physicalGlobalQuery_inactive source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta initial group integer request hinactive]

 theorem physicalRandomGlobalQuery_active_value (request : PhysicalTableRequest M J target.length)
    (hactive : T < request.index ∧ request.node.1.val < J ∧
      ¬ (physicalSourceInterval source.length request.node).hi -
        (physicalSourceInterval source.length request.node).lo ≤ 1)
    (sourceAnswer : σ → ℚ) (values : PhysicalTableRequest M J target.length → ℚ) :
    (physicalRandomGlobalQuery source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta readGroup readInteger initial request).value
      (Sum.elim sourceAnswer (fun child => values child.val)) =
    (physicalRandomDataRequestQuery source target N P F exponent H Q tau
      (refinementFactor (factor request.pass) F) eta kappa delta request.pass request.copy T S
      (request.index - T) (Nat.sub_pos_of_lt hactive.1) request.node hactive.2.1
      (readGroup request.pass request.copy ⟨request.node, hactive.2.1⟩
        (Fin.ofNat R (request.index - T - 1)))
      (readInteger request.pass request.copy ⟨request.node, hactive.2.1⟩
        (Fin.ofNat R (request.index - T - 1))) request.state).value
      (Sum.elim sourceAnswer (fun child => values child.val)) := by
  unfold physicalRandomGlobalQuery
  rw [dite_eq_left hactive, FiniteQuery.mapKeys_value]
  congr 1
  funext next
  cases next <;> rfl

 theorem physicalRandomGlobalQuery_compare
    (group : ℕ → ℕ → PhysicalInternalNode M J → Fin R → CellGroupDraws M F Q)
    (integer : ℕ → ℕ → PhysicalInternalNode M J → Fin R → ℕ → TargetInterval target.length → ℕ)
    (sourceAnswer : σ → ℚ) (values : PhysicalTableRequest M J target.length → ℚ)
    (hgroup : ∀ pass copy node time key, (readGroup pass copy node time key).value sourceAnswer =
      groupScalarValue (group pass copy node time) key)
    (honline : ∀ pass copy (node : PhysicalInternalNode M J) time key,
      (readInteger pass copy node time key
        (keyedOnlineSourceRange source target (physicalSourceInterval source.length node.val)
          P exponent H tau (fun i r => (∑ j : Fin T, values (PhysicalTableRequest.warmup pass copy
            (physicalChild node.val node.property i) j.val r)) / T) key)).value sourceAnswer =
        (integer pass copy node time key.1 key.2 : ℚ))
    (request : PhysicalTableRequest M J target.length) :
    (physicalRandomGlobalQuery source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta readGroup readInteger initial request).value
      (Sum.elim sourceAnswer (fun child => values child.val)) =
    (physicalGlobalQuery source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta group integer initial request).value (fun child => values child.val) := by
  by_cases ha : T < request.index ∧ request.node.1.val < J ∧
      ¬ (physicalSourceInterval source.length request.node).hi -
        (physicalSourceInterval source.length request.node).lo ≤ 1
  · rw [physicalRandomGlobalQuery_active_value source target N P F exponent H Q T S copies
      factor multiplier tau eta kappa delta readGroup readInteger initial request ha sourceAnswer values]
    rw [physicalGlobalQuery_refinement_value source target N P F exponent H Q T S copies
      factor multiplier tau eta kappa delta group integer initial request ha.1 ha.2.1 ha.2.2 values]
    let node : PhysicalInternalNode M J := ⟨request.node, ha.2.1⟩
    let time : Fin R := Fin.ofNat R (request.index - T - 1)
    have hg := hgroup request.pass request.copy node time
    have hi := honline request.pass request.copy node time
    have hnew := physicalRandomDataRequestQuery_value source target N P F exponent H Q tau
      (refinementFactor (factor request.pass) F) eta kappa delta request.pass request.copy T S
      (request.index - T) (Nat.sub_pos_of_lt ha.1) request.node ha.2.1
      (readGroup request.pass request.copy node time) (readInteger request.pass request.copy node time)
      request.state values sourceAnswer (group request.pass request.copy node time)
      (integer request.pass request.copy node time) hg hi
    have hold := physicalRefinementDataRequestQuery_value source target N P F exponent H Q tau
      (refinementFactor (factor request.pass) F) eta kappa delta request.pass request.copy T S
      (request.index - T) (Nat.sub_pos_of_lt ha.1) request.node ha.2.1
      (group request.pass request.copy node time) (integer request.pass request.copy node time)
      request.state values
    exact hnew.trans hold.symm
  · rw [physicalRandomGlobalQuery_inactive source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta readGroup readInteger initial group integer request ha, FiniteQuery.mapKeys_value]
    rfl

end Global

end EditApproximation

end OAI
