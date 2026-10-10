import OAI.Combinatorics.EditApproximation.Refinement.PhysicalRandomBoundedQuery
import OAI.Combinatorics.EditApproximation.Refinement.PhysicalRandomGlobalProgress

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
  (sourceValue : σ → ℚ) (tableValue : PhysicalTableRequest M J target.length → ℚ)

 theorem physicalRandomBoundedQuery_cost (sourceWeight : σ → ℕ)
    (tableWeight : PhysicalTableRequest M J target.length → ℕ)
    (request : {request : PhysicalTableRequest M J target.length // request.Bounded passes copies T S}) :
    (physicalRandomBoundedQuery source target N P F exponent H Q T S passes copies factor multiplier
      tau eta kappa delta readGroup readInteger initial request).cost
      (Sum.elim sourceValue (fun child => tableValue child.val.val))
      (Sum.elim sourceWeight (fun child => tableWeight child.val.val)) =
    (physicalRandomGlobalQuery source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta readGroup readInteger initial request.val).cost
      (Sum.elim sourceValue (fun child => tableValue child.val))
      (Sum.elim sourceWeight (fun child => tableWeight child.val)) := by
  unfold physicalRandomBoundedQuery
  exact SourceRanked.restrictBody_cost _ _ _ _ _ _ _ request
    (physicalRandomGlobalQuery_keys_bounded source target N P F exponent H Q T S passes copies
      factor multiplier tau eta kappa delta readGroup readInteger initial request.val request.property _)

 theorem physicalRandomBoundedQuery_progress
    (request : {request : PhysicalTableRequest M J target.length // request.Bounded passes copies T S}) :
    ∀ key ∈ (physicalRandomBoundedQuery source target N P F exponent H Q T S passes copies
      factor multiplier tau eta kappa delta readGroup readInteger initial request).keys
        (Sum.elim sourceValue (fun child => tableValue child.val.val)),
      match key with
      | .inl _ => True
      | .inr child => PhysicalTableRequest.DependencyProgress T S request.val child.val.val := by
  unfold physicalRandomBoundedQuery
  have hall := SourceRanked.restrictBody_keys_all _ _ _ sourceValue tableValue (fun _ => True)
    (PhysicalTableRequest.DependencyProgress T S request.val) request
    (physicalRandomGlobalQuery_keys_bounded source target N P F exponent H Q T S passes copies
      factor multiplier tau eta kappa delta readGroup readInteger initial request.val request.property _)
    (by
      intro key hk
      have h := physicalRandomGlobalQuery_keys_progress source target N P F exponent H Q T S copies
        factor multiplier tau eta kappa delta readGroup readInteger initial request.val
        (Sum.elim sourceValue (fun child => tableValue child.val)) key hk
      cases key <;> exact h)
  intro key hk
  have h := hall key hk
  cases key <;> exact h

end Bounded

end EditApproximation

end OAI
