import OAI.Combinatorics.EditApproximation.Refinement.PhysicalRandomDataRequest
import OAI.Combinatorics.EditApproximation.Geometry.LocalRandomQueryKeys
import OAI.Combinatorics.EditApproximation.Refinement.PhysicalQueryProgress

namespace OAI

/-! Adding source reads preserves the actual tree/index progress of all
physical table dependencies. Source coordinates have no table dependency. -/

namespace EditApproximation

 theorem physicalRandomDataRequest_keys_progress {σ α : Type*} (source target : List α)
    {M J : ℕ} [NeZero M] (N P F exponent H Q : ℕ) (tau a eta kappa delta : ℚ)
    (pass copy T S t : ℕ) (ht : 0 < t)
    (node : PhysicalNode M J) (hbelow : node.1.val < J)
    (readGroup : GroupScalarKey M F Q → FiniteQuery σ)
    (readInteger : (ℕ × TargetInterval target.length) → ℕ → FiniteQuery σ)
    (q : TargetInterval target.length) (oracle) :
    ∀ key ∈ (physicalRandomDataRequestQuery source target N P F exponent H Q tau a eta kappa delta
      pass copy T S t ht node hbelow readGroup readInteger q).keys oracle,
      match key with
      | .inl _ => True
      | .inr table => PhysicalTableRequest.DependencyProgress T S
          (PhysicalTableRequest.refinement pass copy node T t q) table.val := by
  unfold physicalRandomDataRequestQuery
  apply localRandomDataQuery_keys_all
  · intro input
    apply FiniteQuery.keys_all_mapKeys
    intro key _
    trivial
  · intro input range
    apply FiniteQuery.keys_all_mapKeys
    intro key _
    trivial
  · intro input
    apply FiniteQuery.keys_all_mapKeys
    intro key hk
    unfold physicalRefinementEarlierQuery at hk
    split_ifs at hk with hs
    · simp only [FiniteQuery.keys, List.mem_singleton] at hk
      subst key
      exact PhysicalTableRequest.refinement_child_earlier_progress pass copy T S t input.2.1
        node hbelow input.1 q input.2.2 hs
    · exact False.elim (List.not_mem_nil hk)
  · intro input
    apply FiniteQuery.keys_all_mapKeys
    intro key hk
    simp only [physicalRefinementCurrentQuery, FiniteQuery.keys, List.mem_singleton] at hk
    subst key
    exact PhysicalTableRequest.refinement_child_same_progress pass copy T S t node hbelow input.1 q input.2
  · intro r
    apply FiniteQuery.keys_all_mapKeys
    intro key hk
    exact physicalRefinementWarmupRead_keys_progress pass copy T S t ht node q node le_rfl
      0 (Nat.zero_le T) r _ key hk
  · intro input
    apply FiniteQuery.keys_all_mapKeys
    unfold physicalRefinementMassQuery
    apply FiniteQuery.keys_all_collect
    · intro j _ key hk
      exact physicalRefinementWarmupRead_keys_progress pass copy T S t ht node q
        (physicalChild node hbelow input.1) _ j.val (Nat.le_of_lt j.isLt) input.2 _ key hk
    · intro values key hk
      exact False.elim (List.not_mem_nil hk)
  · intro input
    apply FiniteQuery.keys_all_mapKeys
    intro key hk
    exact physicalRefinementWarmupRead_keys_progress pass copy T S t ht node q
      (physicalChild node hbelow input.1) _ 0 (Nat.zero_le T) input.2 _ key hk

end EditApproximation

end OAI
