import OAI.Combinatorics.EditApproximation.Refinement.PhysicalRandomDataRequest
import OAI.Combinatorics.EditApproximation.Geometry.LocalRandomQueryKeys
import OAI.Combinatorics.EditApproximation.Refinement.PhysicalQueryProgress

namespace OAI

/-! Every recursive table read of an adaptive random query stays in the same
pass and copy and has no larger local index. -/

namespace EditApproximation

 theorem physicalRandomDataRequest_keys_pass_copy {σ α : Type*} (source target : List α)
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
      | .inr table => table.val.pass = pass ∧ table.val.copy = copy ∧ table.val.index ≤ T + t := by
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
      exact ⟨rfl, rfl, by change T + input.2.1 ≤ T + t; omega⟩
    · exact False.elim (List.not_mem_nil hk)
  · intro input
    apply FiniteQuery.keys_all_mapKeys
    intro key hk
    simp only [physicalRefinementCurrentQuery, FiniteQuery.keys, List.mem_singleton] at hk
    subst key
    exact ⟨rfl, rfl, le_rfl⟩
  · intro r
    apply FiniteQuery.keys_all_mapKeys
    intro key hk
    exact physicalRefinementWarmupRead_keys_pass_copy pass copy T S t ht node q node le_rfl
      0 (Nat.zero_le T) r _ key hk
  · intro input
    apply FiniteQuery.keys_all_mapKeys
    unfold physicalRefinementMassQuery
    apply FiniteQuery.keys_all_collect
    · intro j _ key hk
      exact physicalRefinementWarmupRead_keys_pass_copy pass copy T S t ht node q
        (physicalChild node hbelow input.1) _ j.val (Nat.le_of_lt j.isLt) input.2 _ key hk
    · intro values key hk
      exact False.elim (List.not_mem_nil hk)
  · intro input
    apply FiniteQuery.keys_all_mapKeys
    intro key hk
    exact physicalRefinementWarmupRead_keys_pass_copy pass copy T S t ht node q
      (physicalChild node hbelow input.1) _ 0 (Nat.zero_le T) input.2 _ key hk

end EditApproximation

end OAI
