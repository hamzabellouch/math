import OAI.Combinatorics.EditApproximation.Refinement.PhysicalRandomBoundedQuery
import OAI.Combinatorics.EditApproximation.Geometry.ChargedGlobalQuery
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! The coarse seed, recursive table values, and random scalar sources are
all requested through the memo program. Inactive refinement branches use
the existing explicit coarse/median seed queries. -/

namespace EditApproximation

section Global

variable {σ α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R]
  (source target : List α) (N P F exponent H Q T S passes copies : ℕ)
  (factor : ℕ → ℚ) (multiplier : ℕ → ℕ) (tau eta kappa delta : ℚ)
  (readGroup : ℕ → ℕ → PhysicalInternalNode M J → Fin R → GroupScalarKey M F Q → FiniteQuery σ)
  (readInteger : ℕ → ℕ → PhysicalInternalNode M J → Fin R →
    (ℕ × TargetInterval target.length) → ℕ → FiniteQuery σ)
  (initial : PhysicalEntry M J target.length → ℕ)



variable
  (group : ℕ → ℕ → PhysicalInternalNode M J → Fin R → CellGroupDraws M F Q)
  (integer : ℕ → ℕ → PhysicalInternalNode M J → Fin R → ℕ → TargetInterval target.length → ℕ)
  (sourceAnswer : σ → ℚ)

/-- Composition with the local source-provider correctness theorem. -/
 theorem chargedRandomGlobalQuery_value
    (hbody : ∀ parent,
      (physicalRandomBoundedQuery source target N P F exponent H Q T S passes copies factor multiplier
        tau eta kappa delta readGroup readInteger initial parent).value
        (Sum.elim sourceAnswer (fun child => localRequestValue source target N P F exponent H Q T S copies
          factor multiplier tau eta kappa delta group integer initial child.val.val)) =
      localRequestValue source target N P F exponent H Q T S copies factor multiplier
        tau eta kappa delta group integer initial parent.val)
    (request : ChargedPhysicalRequest M J target.length passes copies T S) :
    (chargedRandomGlobalQuery source target N P F exponent H Q T S passes copies factor multiplier
      tau eta kappa delta readGroup readInteger initial request).value
      (Sum.elim sourceAnswer (fun child => chargedRequestValue source target N P F exponent H Q T S
        passes copies factor multiplier tau eta kappa delta group integer initial child.val)) =
    chargedRequestValue source target N P F exponent H Q T S passes copies factor multiplier
      tau eta kappa delta group integer initial request := by
  cases request with
  | inl entry => rfl
  | inr parent =>
    change _ = localRequestValue source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta group integer initial parent.val
    unfold chargedRandomGlobalQuery
    dsimp only
    split_ifs with hi hd hw
    · rw [FiniteQuery.mapKeys_value]
      exact chargedWarmupQuery_value source target N P F exponent H Q T S passes copies
        factor multiplier tau eta kappa delta group integer initial parent hi
    · rw [FiniteQuery.mapKeys_value,
        localRequestValue_terminal source target N P F exponent H Q T S copies factor multiplier
          tau eta kappa delta group integer initial parent.val (Or.inr hw)]
      exact physicalInitialQuery_value_local source target N P F _ _ _ _ _ _
        (chargedSeedQuery_localValue source target N P F exponent H Q T S passes copies
          factor multiplier tau eta kappa delta group integer initial parent)
    · rw [FiniteQuery.mapKeys_value]
      refine Eq.trans ?_ (hbody parent)
      congr 1
      funext next
      cases next <;> rfl
    · rw [FiniteQuery.mapKeys_value,
        localRequestValue_terminal source target N P F exponent H Q T S copies factor multiplier
          tau eta kappa delta group integer initial parent.val (Or.inl hd)]
      exact physicalInitialQuery_value_local source target N P F _ _ _ _ _ _
        (chargedSeedQuery_localValue source target N P F exponent H Q T S passes copies
          factor multiplier tau eta kappa delta group integer initial parent)

end Global

end EditApproximation

end OAI
