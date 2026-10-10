import OAI.Combinatorics.EditApproximation.Geometry.ChargedRandomGlobalQuery
import OAI.Combinatorics.EditApproximation.Geometry.ChargedCoarseOracle
import OAI.Combinatorics.EditApproximation.Geometry.SourceRankedWork

namespace OAI

/-! A fixed accepted source family leaves a nonanticipating coarse query:
coarse values enter only when the corresponding leaf is requested. -/

namespace EditApproximation

section Coarse

variable {σ α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R]
  (source target : List α) (N P F exponent H Q T S passes copies : ℕ)
  (factor : ℕ → ℚ) (multiplier : ℕ → ℕ) (tau eta kappa delta : ℚ)
  (readGroup : ℕ → ℕ → PhysicalInternalNode M J → Fin R → GroupScalarKey M F Q → FiniteQuery σ)
  (readInteger : ℕ → ℕ → PhysicalInternalNode M J → Fin R → (ℕ × TargetInterval target.length) → ℕ → FiniteQuery σ)
  (sourceAnswer : σ → ℚ)

theorem physicalRandomGlobalQuery_refinement_initial_independent
    (left right : PhysicalEntry M J target.length → ℕ)
    (parent : PhysicalTableRequest M J target.length)
    (hi : ¬ parent.index ≤ T) (hd : parent.node.1.val < J)
    (hw : ¬ (physicalSourceInterval source.length parent.node).hi -
      (physicalSourceInterval source.length parent.node).lo ≤ 1) :
    physicalRandomGlobalQuery source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta readGroup readInteger left parent =
    physicalRandomGlobalQuery source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta readGroup readInteger right parent := by
  unfold physicalRandomGlobalQuery
  rw [dite_eq_left ⟨by omega, hd, hw⟩, dite_eq_left ⟨by omega, hd, hw⟩]

/-- Coarse answers enter the charged program only at coarse leaves. -/
theorem chargedRandomGlobalQuery_table_initial_independent
    (left right : PhysicalEntry M J target.length → ℕ)
    (parent : {request : PhysicalTableRequest M J target.length // request.Bounded passes copies T S}) :
    chargedRandomGlobalQuery source target N P F exponent H Q T S passes copies factor multiplier
      tau eta kappa delta readGroup readInteger left (.inr parent) =
    chargedRandomGlobalQuery source target N P F exponent H Q T S passes copies factor multiplier
      tau eta kappa delta readGroup readInteger right (.inr parent) := by
  unfold chargedRandomGlobalQuery
  dsimp only
  split_ifs with hi hd hw
  · rfl
  · rfl
  · unfold physicalRandomBoundedQuery SourceRanked.restrictBody
    rw [physicalRandomGlobalQuery_refinement_initial_independent source target N P F exponent H Q T S
      copies factor multiplier tau eta kappa delta readGroup readInteger left right parent.val hi hd hw]
  · rfl

/-- The flattened program receives each coarse answer from an explicit
external read. The constant zero here is never used as a seed answer. -/
noncomputable def chargedRandomCoarseQuery (root : ChargedPhysicalRequest M J target.length passes copies T S) :
    FiniteQuery (PhysicalEntry M J target.length) :=
  match root with
  | .inl entry => .read entry FiniteQuery.done
  | .inr parent =>
    (SourceRanked.projectedBody ChargedPhysicalRequest.rank
      (chargedRandomGlobalQuery source target N P F exponent H Q T S passes copies factor multiplier
        tau eta kappa delta readGroup readInteger (fun _ => 0)) sourceAnswer (.inr parent)).substitute
        (fun child => chargedRandomCoarseQuery child.val)
termination_by root.rank
decreasing_by exact child.property

theorem chargedRandomCoarseQuery_value
    (initial : PhysicalEntry M J target.length → ℕ)
    (root : ChargedPhysicalRequest M J target.length passes copies T S) :
    (chargedRandomCoarseQuery source target N P F exponent H Q T S passes copies factor multiplier
      tau eta kappa delta readGroup readInteger sourceAnswer root).value (fun entry => (initial entry : ℚ)) =
    rankedProgramValue ChargedPhysicalRequest.rank
      (SourceRanked.projectedBody ChargedPhysicalRequest.rank
        (chargedRandomGlobalQuery source target N P F exponent H Q T S passes copies factor multiplier
          tau eta kappa delta readGroup readInteger initial) sourceAnswer) root := by
  have hall : ∀ level root, root.rank = level →
      (chargedRandomCoarseQuery source target N P F exponent H Q T S passes copies factor multiplier
        tau eta kappa delta readGroup readInteger sourceAnswer root).value (fun entry => (initial entry : ℚ)) =
      rankedProgramValue ChargedPhysicalRequest.rank
        (SourceRanked.projectedBody ChargedPhysicalRequest.rank
          (chargedRandomGlobalQuery source target N P F exponent H Q T S passes copies factor multiplier
            tau eta kappa delta readGroup readInteger initial) sourceAnswer) root := by
    intro level
    induction level using Nat.strong_induction_on with
    | h level ih =>
      intro root hlevel
      cases root with
      | inl entry =>
        rw [chargedRandomCoarseQuery, rankedProgramValue]
        rfl
      | inr parent =>
        rw [chargedRandomCoarseQuery, FiniteQuery.substitute_value, rankedProgramValue]
        unfold SourceRanked.projectedBody
        rw [
          chargedRandomGlobalQuery_table_initial_independent source target N P F exponent H Q T S passes copies
            factor multiplier tau eta kappa delta readGroup readInteger (fun _ => 0) initial parent]
        congr 1
        funext child
        exact ih child.val.rank (hlevel ▸ child.property) child.val rfl
  exact hall root.rank root rfl

end Coarse

end EditApproximation

end OAI
