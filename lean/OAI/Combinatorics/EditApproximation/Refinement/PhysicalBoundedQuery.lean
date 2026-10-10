import OAI.Combinatorics.EditApproximation.Refinement.PhysicalGlobalValue
import OAI.Combinatorics.EditApproximation.Refinement.PhysicalRefinementReadWork
import OAI.Combinatorics.EditApproximation.Geometry.WarmupQueryKeys
import OAI.Combinatorics.EditApproximation.Geometry.RankedProgramRestriction
import OAI.Combinatorics.EditApproximation.Refinement.PhysicalRequestEncoding

namespace OAI

/-! The actual global read program stays within the bounded cache-key
domain. Restricting its type therefore preserves the complete local-pass
value and gives an injectively encoded memo evaluator. -/

namespace EditApproximation

instance PhysicalTableRequest.decidableBounded {M J ny : ℕ} (passes copies T S : ℕ) :
    DecidablePred (PhysicalTableRequest.Bounded (M := M) (J := J) (ny := ny) passes copies T S) :=
  fun request => inferInstanceAs (Decidable
    (request.pass < passes ∧ request.copy < copies ∧ request.index ≤ T + S))

theorem globalSeedRead_keys_bounded {M J ny : ℕ} (N T S passes copies : ℕ)
    (multiplier : ℕ → ℕ) (initial : PhysicalEntry M J ny → ℕ)
    (parent : PhysicalTableRequest M J ny) (hparent : parent.Bounded passes copies T S)
    (state : PhysicalEntry M J ny) (oracle) :
    ∀ key ∈ (globalSeedRead N T S copies multiplier initial parent state).keys oracle,
      key.val.Bounded passes copies T S := by
  unfold globalSeedRead
  split_ifs with hnode hpass
  · intro key hk
    exact False.elim (List.not_mem_nil hk)
  · unfold physicalMedianSeedQuery
    apply FiniteQuery.keys_all_collect
    · intro copy _ key hk
      simp only [previousPassRead, FiniteQuery.keys, List.mem_singleton] at hk
      subst key
      exact ⟨Nat.lt_of_le_of_lt (Nat.sub_le _ _) hparent.1, copy.isLt, le_rfl⟩
    · intro values key hk
      exact False.elim (List.not_mem_nil hk)
  · intro key hk
    exact False.elim (List.not_mem_nil hk)

section Bounded

variable {α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero R]
  (source target : List α) (N P F exponent H Q T S passes copies : ℕ)
  (factor : ℕ → ℚ) (multiplier : ℕ → ℕ) (tau eta kappa delta : ℚ)
  (group : ℕ → ℕ → PhysicalInternalNode M J → Fin R → CellGroupDraws M F Q)
  (integer : ℕ → ℕ → PhysicalInternalNode M J → Fin R → ℕ → TargetInterval target.length → ℕ)
  (initial : PhysicalEntry M J target.length → ℕ)

theorem physicalGlobalQuery_keys_bounded (request : PhysicalTableRequest M J target.length)
    (hrequest : request.Bounded passes copies T S) (oracle) :
    ∀ key ∈ (physicalGlobalQuery source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta group integer initial request).keys oracle,
      key.val.Bounded passes copies T S := by
  rcases request with ⟨pass, copy, node, index, q⟩
  obtain ⟨hpass, hcopy, hindex⟩ := hrequest
  dsimp only at hpass hcopy hindex
  by_cases hj : index ≤ T
  · change ∀ key ∈ (physicalGlobalQuery source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta group integer initial (PhysicalTableRequest.warmup pass copy node index q)).keys oracle,
        key.val.Bounded passes copies T S
    rw [physicalGlobalQuery_warmup source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta group integer initial pass copy node index hj q]
    apply physicalWarmupRequestQuery_keys_bounded source target N P F (factor pass)
      passes copies pass copy T S index hpass hcopy hj node q _ oracle
    intro r key hk
    exact globalSeedRead_keys_bounded N T S passes copies multiplier initial _
      ⟨hpass, hcopy, hindex⟩ _ oracle key hk
  · obtain ⟨t, hi⟩ : ∃ t, index = T + t := ⟨index - T, by omega⟩
    subst index
    have ht : 0 < t := by omega
    have htS : t ≤ S := by omega
    change ∀ key ∈ (physicalGlobalQuery source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta group integer initial (PhysicalTableRequest.refinement pass copy node T t q)).keys oracle,
        key.val.Bounded passes copies T S
    by_cases hbelow : node.1.val < J
    · by_cases hshort : (physicalSourceInterval source.length node).hi -
          (physicalSourceInterval source.length node).lo ≤ 1
      · unfold physicalGlobalQuery
        dsimp only
        erw [dite_eq_right (show ¬ (PhysicalTableRequest.refinement pass copy node T t q).index ≤ T
          from hj), dite_eq_left hbelow, dite_eq_left hshort]
        apply physicalInitialQuery_keys_all
        intro r key hk
        exact globalSeedRead_keys_bounded N T S passes copies multiplier initial _
          ⟨hpass, hcopy, hindex⟩ _ oracle key hk
      · unfold physicalGlobalQuery
        dsimp only
        erw [dite_eq_right (show ¬ (PhysicalTableRequest.refinement pass copy node T t q).index ≤ T
          from hj), dite_eq_left hbelow, dite_eq_right hshort]
        erw [FiniteQuery.mapKeys_keys]
        intro key hk
        obtain ⟨child, hc, rfl⟩ := List.mem_map.mp hk
        exact physicalRefinementDataRequest_keys_bounded source target N P F exponent H Q tau
          (refinementFactor (factor pass) F) eta kappa delta passes copies pass copy T S
          (T + t - T) (by omega) (by omega) hpass hcopy node hbelow _ _ q _ child hc
    · unfold physicalGlobalQuery
      dsimp only
      erw [dite_eq_right (show ¬ (PhysicalTableRequest.refinement pass copy node T t q).index ≤ T
        from hj), dite_eq_right hbelow]
      apply physicalInitialQuery_keys_all
      intro r key hk
      exact globalSeedRead_keys_bounded N T S passes copies multiplier initial _
        ⟨hpass, hcopy, hindex⟩ _ oracle key hk

def physicalBoundedQuery
    (request : {request : PhysicalTableRequest M J target.length // request.Bounded passes copies T S}) :
    FiniteQuery {child : {child : PhysicalTableRequest M J target.length // child.Bounded passes copies T S} //
      child.val.combinedRank T S < request.val.combinedRank T S} :=
  restrictRankedProgram (PhysicalTableRequest.combinedRank T S)
    (physicalGlobalQuery source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta group integer initial) (PhysicalTableRequest.Bounded passes copies T S) request

theorem physicalBoundedQuery_value
    (request : {request : PhysicalTableRequest M J target.length // request.Bounded passes copies T S}) :
    (physicalBoundedQuery source target N P F exponent H Q T S passes copies factor multiplier
      tau eta kappa delta group integer initial request).value
        (fun child => localRequestValue source target N P F exponent H Q T S copies factor multiplier
          tau eta kappa delta group integer initial child.val.val) =
    localRequestValue source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta group integer initial request.val := by
  unfold physicalBoundedQuery
  rw [restrictRankedProgram_value _ _ _ _ request
    (physicalGlobalQuery_keys_bounded source target N P F exponent H Q T S passes copies factor multiplier
      tau eta kappa delta group integer initial request.val request.property _)]
  exact physicalGlobalQuery_value source target N P F exponent H Q T S copies factor multiplier
    tau eta kappa delta group integer initial request.val

def physicalMemoEvaluate
    (request : {request : PhysicalTableRequest M J target.length // request.Bounded passes copies T S}) :=
  rankedMemoEvaluate (fun request :
      {request : PhysicalTableRequest M J target.length // request.Bounded passes copies T S} =>
      request.val.combinedRank T S)
    (physicalBoundedQuery source target N P F exponent H Q T S passes copies factor multiplier
      tau eta kappa delta group integer initial)
    (PhysicalTableRequest.bits M J target.length passes copies T S)
    (fun request => PhysicalTableRequest.code copies T S request.val) request .empty

theorem physicalMemoEvaluate_value (hM : 1 ≤ M)
    (request : {request : PhysicalTableRequest M J target.length // request.Bounded passes copies T S}) :
    (physicalMemoEvaluate source target N P F exponent H Q T S passes copies factor multiplier
      tau eta kappa delta group integer initial request).value =
    localRequestValue source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta group integer initial request.val := by
  unfold physicalMemoEvaluate
  exact rankedMemoEvaluate_specification
    (fun request : {request : PhysicalTableRequest M J target.length //
      request.Bounded passes copies T S} => request.val.combinedRank T S)
    (physicalBoundedQuery source target N P F exponent H Q T S passes copies factor multiplier
      tau eta kappa delta group integer initial)
    (fun request => localRequestValue source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta group integer initial request.val)
    (physicalBoundedQuery_value source target N P F exponent H Q T S passes copies factor multiplier
      tau eta kappa delta group integer initial)
    _ _ (PhysicalTableRequest.code_injective hM passes copies T S)
    (PhysicalTableRequest.code_fits hM passes copies T S) request

end Bounded

end EditApproximation

end OAI
