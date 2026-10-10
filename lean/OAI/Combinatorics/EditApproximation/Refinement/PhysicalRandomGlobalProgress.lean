import OAI.Combinatorics.EditApproximation.Refinement.PhysicalRandomGlobalQuery
import OAI.Combinatorics.EditApproximation.Refinement.PhysicalRandomRequestProgress
import OAI.Combinatorics.EditApproximation.Geometry.GlobalQueryProgress

namespace OAI

namespace EditApproximation

section Progress

variable {σ α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R]
  (source target : List α) (N P F exponent H Q T S copies : ℕ)
  (factor : ℕ → ℚ) (multiplier : ℕ → ℕ) (tau eta kappa delta : ℚ)
  (readGroup : ℕ → ℕ → PhysicalInternalNode M J → Fin R → GroupScalarKey M F Q → FiniteQuery σ)
  (readInteger : ℕ → ℕ → PhysicalInternalNode M J → Fin R →
    (ℕ × TargetInterval target.length) → ℕ → FiniteQuery σ)
  (initial : PhysicalEntry M J target.length → ℕ)

 theorem physicalRandomGlobalQuery_keys_progress (request : PhysicalTableRequest M J target.length)
    (oracle) :
    ∀ key ∈ (physicalRandomGlobalQuery source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta readGroup readInteger initial request).keys oracle,
      match key with
      | .inl _ => True
      | .inr table => PhysicalTableRequest.DependencyProgress T S request table.val := by
  unfold physicalRandomGlobalQuery
  by_cases ha : T < request.index ∧ request.node.1.val < J ∧
      ¬ (physicalSourceInterval source.length request.node).hi -
        (physicalSourceInterval source.length request.node).lo ≤ 1
  · rw [dite_eq_left ha, FiniteQuery.mapKeys_keys]
    intro key hk
    obtain ⟨other, ho, rfl⟩ := List.mem_map.mp hk
    have hi := physicalRandomDataRequest_keys_progress source target N P F exponent H Q tau
      (refinementFactor (factor request.pass) F) eta kappa delta request.pass request.copy T S
      (request.index - T) (Nat.sub_pos_of_lt ha.1) request.node ha.2.1
      (readGroup request.pass request.copy ⟨request.node, ha.2.1⟩ (Fin.ofNat R (request.index - T - 1)))
      (readInteger request.pass request.copy ⟨request.node, ha.2.1⟩ (Fin.ofNat R (request.index - T - 1)))
      request.state _ other ho
    have heq : PhysicalTableRequest.refinement request.pass request.copy request.node
        T (request.index - T) request.state = request := by
      unfold PhysicalTableRequest.refinement
      have ht : T + (request.index - T) = request.index :=
        Nat.add_sub_of_le (Nat.le_of_lt ha.1)
      rw [ht]
    cases other with
    | inl key => trivial
    | inr table => simpa only [Sum.map_inr, heq] using hi
  · rw [dite_eq_right ha, FiniteQuery.mapKeys_keys]
    intro key hk
    obtain ⟨other, ho, rfl⟩ := List.mem_map.mp hk
    rw [physicalGlobalQuery_inactive (R := R) source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta initial (fun _ _ _ _ _ _ _ _ => 0) (fun _ _ _ _ _ _ => 0) request ha] at ho
    exact physicalGlobalQuery_keys_progress (R := R) source target N P F exponent H Q T S copies
      factor multiplier tau eta kappa delta (fun _ _ _ _ _ _ _ _ => 0) (fun _ _ _ _ _ _ => 0)
      initial request _ other ho

end Progress

end EditApproximation

end OAI
