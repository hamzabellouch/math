import OAI.Combinatorics.EditApproximation.Refinement.PhysicalRandomGlobalQuery
import OAI.Combinatorics.EditApproximation.Refinement.PhysicalRandomRequestBounds
import OAI.Combinatorics.EditApproximation.Refinement.PhysicalBoundedQuery
import OAI.Combinatorics.EditApproximation.Geometry.SourceRankedRestriction
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

namespace EditApproximation

section Bounded

variable {σ α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R]
  (source target : List α) (N P F exponent H Q T S passes copies : ℕ)
  (factor : ℕ → ℚ) (multiplier : ℕ → ℕ) (tau eta kappa delta : ℚ)
  (readGroup : ℕ → ℕ → PhysicalInternalNode M J → Fin R → GroupScalarKey M F Q → FiniteQuery σ)
  (readInteger : ℕ → ℕ → PhysicalInternalNode M J → Fin R →
    (ℕ × TargetInterval target.length) → ℕ → FiniteQuery σ)
  (initial : PhysicalEntry M J target.length → ℕ)

 theorem physicalRandomGlobalQuery_keys_bounded (request : PhysicalTableRequest M J target.length)
    (hrequest : request.Bounded passes copies T S) (oracle) :
    ∀ key ∈ (physicalRandomGlobalQuery source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta readGroup readInteger initial request).keys oracle,
      SourceRanked.supportedChild (PhysicalTableRequest.combinedRank T S)
        (PhysicalTableRequest.Bounded passes copies T S) request key := by
  unfold physicalRandomGlobalQuery
  by_cases ha : T < request.index ∧ request.node.1.val < J ∧
      ¬ (physicalSourceInterval source.length request.node).hi -
        (physicalSourceInterval source.length request.node).lo ≤ 1
  · rw [dite_eq_left ha, FiniteQuery.mapKeys_keys]
    intro key hk
    obtain ⟨other, ho, rfl⟩ := List.mem_map.mp hk
    have hi := physicalRandomDataRequest_keys_bounded source target N P F exponent H Q tau
      (refinementFactor (factor request.pass) F) eta kappa delta passes copies request.pass request.copy T S
      (request.index - T) (Nat.sub_pos_of_lt ha.1) (by have := hrequest.2.2; omega)
      hrequest.1 hrequest.2.1 request.node ha.2.1
      (readGroup request.pass request.copy ⟨request.node, ha.2.1⟩ (Fin.ofNat R (request.index - T - 1)))
      (readInteger request.pass request.copy ⟨request.node, ha.2.1⟩ (Fin.ofNat R (request.index - T - 1)))
      request.state _ other ho
    cases other <;> exact hi
  · rw [dite_eq_right ha, FiniteQuery.mapKeys_keys]
    intro key hk
    obtain ⟨other, ho, rfl⟩ := List.mem_map.mp hk
    rw [physicalGlobalQuery_inactive (R := R) source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta initial (fun _ _ _ _ _ _ _ _ => 0) (fun _ _ _ _ _ _ => 0) request ha] at ho
    exact physicalGlobalQuery_keys_bounded (R := R) source target N P F exponent H Q T S passes copies
      factor multiplier tau eta kappa delta (fun _ _ _ _ _ _ _ _ => 0) (fun _ _ _ _ _ _ => 0)
      initial request hrequest _ other ho



 theorem physicalRandomBoundedQuery_value
    (sourceValue : σ → ℚ) (tableValue : PhysicalTableRequest M J target.length → ℚ)
    (request : {request : PhysicalTableRequest M J target.length // request.Bounded passes copies T S}) :
    (physicalRandomBoundedQuery source target N P F exponent H Q T S passes copies factor multiplier
      tau eta kappa delta readGroup readInteger initial request).value
        (Sum.elim sourceValue (fun key => tableValue key.val.val)) =
    (physicalRandomGlobalQuery source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta readGroup readInteger initial request.val).value
        (Sum.elim sourceValue (fun key => tableValue key.val)) := by
  unfold physicalRandomBoundedQuery
  exact SourceRanked.restrictBody_value _ _ _ _ _ request
    (physicalRandomGlobalQuery_keys_bounded source target N P F exponent H Q T S passes copies
      factor multiplier tau eta kappa delta readGroup readInteger initial request.val request.property _)

end Bounded

end EditApproximation

end OAI
