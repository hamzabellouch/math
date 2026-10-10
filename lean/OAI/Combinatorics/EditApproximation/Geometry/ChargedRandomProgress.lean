import OAI.Combinatorics.EditApproximation.Geometry.ChargedRandomGlobalQuery
import OAI.Combinatorics.EditApproximation.Refinement.PhysicalRandomBoundedCost
import OAI.Combinatorics.EditApproximation.Geometry.ChargedQueryProgress

namespace OAI

/-! Actual mixed requests retain the charged physical depth/index progress.
This statement holds for every returned source and table value. -/

namespace EditApproximation

section Global

variable {σ α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R]
  (source target : List α) (N P F exponent H Q T S passes copies : ℕ)
  (factor : ℕ → ℚ) (multiplier : ℕ → ℕ) (tau eta kappa delta : ℚ)
  (readGroup : ℕ → ℕ → PhysicalInternalNode M J → Fin R → GroupScalarKey M F Q → FiniteQuery σ)
  (readInteger : ℕ → ℕ → PhysicalInternalNode M J → Fin R →
    (ℕ × TargetInterval target.length) → ℕ → FiniteQuery σ)
  (initial : PhysicalEntry M J target.length → ℕ)
  (sourceAnswer : σ → ℚ)
  (answer : ChargedPhysicalRequest M J target.length passes copies T S → ℚ)

 theorem chargedRandomGlobalQuery_keys_progress
    (request : ChargedPhysicalRequest M J target.length passes copies T S) :
    ∀ key ∈ (chargedRandomGlobalQuery source target N P F exponent H Q T S passes copies
      factor multiplier tau eta kappa delta readGroup readInteger initial request).keys
        (Sum.elim sourceAnswer (fun child => answer child.val)),
      match key with
      | .inl _ => True
      | .inr child => ChargedPhysicalRequest.DependencyProgress request child.val := by
  cases request with
  | inl entry =>
    intro key hk
    exact False.elim (List.not_mem_nil hk)
  | inr parent =>
    unfold chargedRandomGlobalQuery
    dsimp only
    split_ifs with hi hb hs
    · apply FiniteQuery.keys_all_mapKeys
      intro key hk
      exact Or.inr (chargedWarmupQuery_keys_earlier source target N P F factor multiplier parent _ key hk)
    · apply FiniteQuery.keys_all_mapKeys
      intro key hk
      apply Or.inr
      apply physicalInitialQuery_keys_all source target N P F _ _ _ _ _ _ _ key hk
      intro q
      exact chargedSeedQuery_keys_earlier N multiplier parent (parent.val.node, q) _
    · rw [FiniteQuery.mapKeys_keys]
      intro key hk
      obtain ⟨child, hc, rfl⟩ := List.mem_map.mp hk
      let tableMap :
          {child : {r : PhysicalTableRequest M J target.length // r.Bounded passes copies T S} //
            child.val.combinedRank T S < parent.val.combinedRank T S} →
          {child : ChargedPhysicalRequest M J target.length passes copies T S //
            child.rank < ChargedPhysicalRequest.rank (.inr parent)} :=
        fun child => ⟨.inr child.val,
          ChargedPhysicalRequest.table_rank_lt parent child.val child.property⟩
      have horacle : (Sum.elim sourceAnswer (fun child => answer child.val)) ∘
          Sum.map (id : σ → σ) tableMap =
          Sum.elim sourceAnswer (fun child => answer (Sum.inr child.val)) := by
        funext key
        cases key <;> rfl
      rw [horacle] at hc
      have hp := physicalRandomBoundedQuery_progress source target N P F exponent H Q T S passes copies
        factor multiplier tau eta kappa delta readGroup readInteger initial sourceAnswer
        (fun r => if hr : r.Bounded passes copies T S then answer (.inr ⟨r, hr⟩) else 0)
        parent
      cases child with
      | inl key => trivial
      | inr child =>
        apply ChargedPhysicalRequest.table_progress
        apply hp (.inr child)
        convert hc using 1
        congr 1
        funext key
        cases key with
        | inl key => rfl
        | inr key => simp only [Sum.elim_inr, dite_eq_left key.val.property]
    · apply FiniteQuery.keys_all_mapKeys
      intro key hk
      apply Or.inr
      apply physicalInitialQuery_keys_all source target N P F _ _ _ _ _ _ _ key hk
      intro q
      exact chargedSeedQuery_keys_earlier N multiplier parent (parent.val.node, q) _

end Global

end EditApproximation

end OAI
