import OAI.Combinatorics.BalancedRyser.Local.LocalFourEvents
import OAI.Combinatorics.BalancedRyser.Local.LocalKernel

namespace OAI

namespace Balanced.Local.FourEvents

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem offsetProbability_le_four (E E₁ E₂ E₃ E₄ : MergedPairs F → Prop)
    (h : ∀ M, E M → E₁ M ∨ E₂ M ∨ E₃ M ∨ E₄ M) :
    offsetProbability E ≤ offsetProbability E₁ + offsetProbability E₂ +
      offsetProbability E₃ + offsetProbability E₄ := by
  unfold offsetProbability
  simp only [← add_div, ← Finset.sum_add_distrib]
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Finset.sum_le_sum
  intro M _
  by_cases he : E M
  · rcases h M he with hh | hh | hh | hh
    all_goals simp only [he, hh, ite_true]
    all_goals split_ifs <;> norm_num
  · simp only [he, ite_false]
    positivity

theorem conditioned_badCover_le_four {b κ : ℕ} (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b) (p : Point F)
    (hb : 3 ≤ b) (hκ : κ ≤ 2) (ha : Eligible P a) :
    conditionedOffsetProbability (Aligned P a bits p) (AdmissibleBadCover P a bits p) ≤
      conditionedOffsetProbability (Aligned P a bits p) (UnusedPrecoverage P a bits p) +
      conditionedOffsetProbability (Aligned P a bits p) (UsedPairExtra P a bits) +
      conditionedOffsetProbability (Aligned P a bits p) (ForbiddenCollinearTriple P a bits p) +
      conditionedOffsetProbability (Aligned P a bits p) (UnusedNoncollinearTriple P a bits) := by
  unfold conditionedOffsetProbability
  rw [← add_div, ← add_div, ← add_div]
  apply div_le_div_of_nonneg_right _ (KernelBridge.offsetProbability_nonneg _)
  apply offsetProbability_le_four
  intro M hM
  rcases admissibleBadCover_four_events P a bits p M hb hκ ha hM.2 with h | h | h | h
  · exact Or.inl ⟨hM.1, h⟩
  · exact Or.inr (Or.inl ⟨hM.1, h⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨hM.1, h⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hM.1, h⟩))

end
end Balanced.Local.FourEvents

end OAI
