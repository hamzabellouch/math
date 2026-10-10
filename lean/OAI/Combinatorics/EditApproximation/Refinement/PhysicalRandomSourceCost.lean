import OAI.Combinatorics.EditApproximation.Refinement.PhysicalRandomDataRequest
import OAI.Combinatorics.EditApproximation.Geometry.LocalRandomSourceCost

namespace OAI

namespace EditApproximation

namespace FiniteQuery

 theorem mapRight_source_cost {σ κ : Type*} (query : FiniteQuery κ)
    (source : σ → ℚ) (table : κ → ℚ) (weight : σ → ℕ) :
    (mapKeys Sum.inr query).cost (Sum.elim source table) (Sum.elim weight (fun _ => 0)) = 0 := by
  rw [mapKeys_cost]
  exact cost_zero table query

 theorem mapRight_source_keys {σ κ : Type*} (query : FiniteQuery κ)
    (source : σ → ℚ) (table : κ → ℚ) (weight : σ → ℕ) :
    ∀ key ∈ (mapKeys Sum.inr query).keys (Sum.elim source table),
      (Sum.elim weight (fun _ => 0)) key = 0 := by
  rw [mapKeys_keys]
  intro key hk
  obtain ⟨other, _, rfl⟩ := List.mem_map.mp hk
  rfl

end FiniteQuery

 theorem physicalRandomDataRequest_source_cost_le {σ α : Type*} (source target : List α)
    {M J : ℕ} [NeZero M] (N P F exponent H Q : ℕ) (tau a eta kappa delta : ℚ)
    (pass copy T S t : ℕ) (ht : 0 < t) (node : PhysicalNode M J) (hbelow : node.1.val < J)
    (readGroup : GroupScalarKey M F Q → FiniteQuery σ)
    (readInteger : (ℕ × TargetInterval target.length) → ℕ → FiniteQuery σ)
    (q : TargetInterval target.length) (sourceAnswer : σ → ℚ)
    (answer : PhysicalTableRequest M J target.length → ℚ) (weight : σ → ℕ)
    (groupBound onlineBound : ℕ)
    (hgroup : ∀ key, (readGroup key).cost sourceAnswer weight ≤ groupBound)
    (honline : ∀ key range, (readInteger key range).cost sourceAnswer weight ≤ onlineBound) :
    let initial := fun r => answer (PhysicalTableRequest.warmup pass copy node 0 r)
    (physicalRandomDataRequestQuery source target N P F exponent H Q tau a eta kappa delta
      pass copy T S t ht node hbelow readGroup readInteger q).cost
        (Sum.elim sourceAnswer (fun key => answer key.val)) (Sum.elim weight (fun _ => 0)) ≤
      (groupScalarKeys M F Q (localGroupQueryKeys N F exponent a initial q)).length * groupBound +
      (localOnlineSourceKeys N P F a initial q).length * onlineBound := by
  dsimp only
  unfold physicalRandomDataRequestQuery
  apply localRandomDataQuery_source_cost_le
  · intro input
    exact FiniteQuery.mapRight_source_cost _ _ _ _
  · intro input
    exact FiniteQuery.mapRight_source_cost _ _ _ _
  · intro input
    exact FiniteQuery.mapRight_source_keys _ _ _ _
  · intro input
    exact FiniteQuery.mapRight_source_keys _ _ _ _
  · intro key
    rw [FiniteQuery.mapKeys_cost]
    exact hgroup key
  · intro key range
    rw [FiniteQuery.mapKeys_cost]
    exact honline key range
  · intro r
    exact FiniteQuery.mapRight_source_cost _ _ _ _

end EditApproximation

end OAI
