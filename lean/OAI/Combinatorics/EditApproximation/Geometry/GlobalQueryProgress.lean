import OAI.Combinatorics.EditApproximation.Refinement.PhysicalBoundedQuery
import OAI.Combinatorics.EditApproximation.Refinement.PhysicalQueryProgress

namespace OAI

/-! Concrete depth/pass-index progress is preserved by the finite-domain
transport. The statement concerns the reads executed at the actual values. -/

namespace EditApproximation

theorem globalSeedRead_keys_progress {M J ny : ℕ} (N T S copies : ℕ)
    (multiplier : ℕ → ℕ) (initial : PhysicalEntry M J ny → ℕ)
    (parent : PhysicalTableRequest M J ny) (state : PhysicalEntry M J ny) (oracle) :
    ∀ key ∈ (globalSeedRead N T S copies multiplier initial parent state).keys oracle,
      PhysicalTableRequest.DependencyProgress T S parent key.val := by
  unfold globalSeedRead
  split_ifs with hnode hpass
  · intro key hk
    exact False.elim (List.not_mem_nil hk)
  · unfold physicalMedianSeedQuery
    apply FiniteQuery.keys_all_collect
    · intro copy _ key hk
      simp only [previousPassRead, FiniteQuery.keys, List.mem_singleton] at hk
      subst key
      exact Or.inr ⟨(previousPassRequest_progress T S copy.val parent (Nat.pos_of_ne_zero hpass) state.2).1.le,
        (previousPassRequest_progress T S copy.val parent (Nat.pos_of_ne_zero hpass) state.2).2⟩
    · intro values key hk
      exact False.elim (List.not_mem_nil hk)
  · intro key hk
    exact False.elim (List.not_mem_nil hk)

section Progress

variable {α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero R]
  (source target : List α) (N P F exponent H Q T S passes copies : ℕ)
  (factor : ℕ → ℚ) (multiplier : ℕ → ℕ) (tau eta kappa delta : ℚ)
  (group : ℕ → ℕ → PhysicalInternalNode M J → Fin R → CellGroupDraws M F Q)
  (integer : ℕ → ℕ → PhysicalInternalNode M J → Fin R → ℕ → TargetInterval target.length → ℕ)
  (initial : PhysicalEntry M J target.length → ℕ)

theorem physicalGlobalQuery_keys_progress (request : PhysicalTableRequest M J target.length)
    (oracle) :
    ∀ key ∈ (physicalGlobalQuery source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta group integer initial request).keys oracle,
      PhysicalTableRequest.DependencyProgress T S request key.val := by
  rcases request with ⟨pass, copy, node, index, q⟩
  by_cases hj : index ≤ T
  · change ∀ key ∈ (physicalGlobalQuery source target N P F exponent H Q T S copies factor multiplier
        tau eta kappa delta group integer initial (PhysicalTableRequest.warmup pass copy node index q)).keys oracle,
        PhysicalTableRequest.DependencyProgress T S _ key.val
    rw [physicalGlobalQuery_warmup source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta group integer initial pass copy node index hj q]
    apply physicalWarmupRequestQuery_keys_progress
    intro r key hk
    exact globalSeedRead_keys_progress N T S copies multiplier initial _ _ oracle key hk
  · unfold physicalGlobalQuery
    dsimp only
    erw [dite_eq_right (show ¬ ({pass := pass, copy := copy, node := node, index := index, state := q} :
      PhysicalTableRequest M J target.length).index ≤ T from hj)]
    by_cases hbelow : node.1.val < J
    · erw [dite_eq_left hbelow]
      by_cases hshort : (physicalSourceInterval source.length node).hi -
          (physicalSourceInterval source.length node).lo ≤ 1
      · erw [dite_eq_left hshort]
        apply physicalInitialQuery_keys_all
        intro r key hk
        exact globalSeedRead_keys_progress N T S copies multiplier initial _ _ oracle key hk
      · erw [dite_eq_right hshort, FiniteQuery.mapKeys_keys]
        intro key hk
        obtain ⟨child, hc, rfl⟩ := List.mem_map.mp hk
        have h := physicalRefinementDataRequest_keys_progress source target N P F exponent H Q tau
          (refinementFactor (factor pass) F) eta kappa delta pass copy T S (index - T)
          (by omega) node hbelow _ _ q _ child hc
        have heq : PhysicalTableRequest.refinement pass copy node T (index - T) q =
            ({pass := pass, copy := copy, node := node, index := index, state := q} :
              PhysicalTableRequest M J target.length) := by
          unfold PhysicalTableRequest.refinement
          congr 1
          omega
        simpa only [heq] using h
    · erw [dite_eq_right hbelow]
      apply physicalInitialQuery_keys_all
      intro r key hk
      exact globalSeedRead_keys_progress N T S copies multiplier initial _ _ oracle key hk

theorem physicalBoundedQuery_keys_progress
    (request : {r : PhysicalTableRequest M J target.length // r.Bounded passes copies T S}) :
    ∀ key ∈ (physicalBoundedQuery source target N P F exponent H Q T S passes copies factor multiplier
      tau eta kappa delta group integer initial request).keys
        (fun child => localRequestValue source target N P F exponent H Q T S copies factor multiplier
          tau eta kappa delta group integer initial child.val.val),
      PhysicalTableRequest.DependencyProgress T S request.val key.val.val := by
  intro key hk
  have hkeys := restrictRankedProgram_keys (PhysicalTableRequest.combinedRank T S)
    (physicalGlobalQuery source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta group integer initial) (PhysicalTableRequest.Bounded passes copies T S)
    (localRequestValue source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta group integer initial) request
    (physicalGlobalQuery_keys_bounded source target N P F exponent H Q T S passes copies factor multiplier
      tau eta kappa delta group integer initial request.val request.property _)
  have hm : key.val.val ∈ ((physicalGlobalQuery source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta group integer initial request.val).keys
      (fun child => localRequestValue source target N P F exponent H Q T S copies factor multiplier
        tau eta kappa delta group integer initial child.val)).map Subtype.val := by
    rw [← hkeys]
    exact List.mem_map.mpr ⟨key, hk, rfl⟩
  obtain ⟨child, hc, heq⟩ := List.mem_map.mp hm
  rw [← heq]
  exact physicalGlobalQuery_keys_progress source target N P F exponent H Q T S copies factor multiplier
    tau eta kappa delta group integer initial request.val _ child hc

end Progress

end EditApproximation

end OAI
