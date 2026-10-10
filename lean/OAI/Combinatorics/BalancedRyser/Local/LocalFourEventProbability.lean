import OAI.Combinatorics.BalancedRyser.Local.LocalUnusedEventBridge

namespace OAI

namespace Balanced.Local.UnusedOffsetProbability

noncomputable section
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [Field F] in

theorem offsetProbability_or_le (E G : MergedPairs F → Prop) :
    offsetProbability (fun M => E M ∨ G M) ≤
      offsetProbability E + offsetProbability G := by
  unfold offsetProbability
  rw [← add_div, ← Finset.sum_add_distrib]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro M _
  by_cases hE : E M <;> by_cases hG : G M <;> simp [hE, hG]

theorem conditionedOffsetProbability_or_le (A E G : MergedPairs F → Prop) :
    conditionedOffsetProbability A (fun M => E M ∨ G M) ≤
      conditionedOffsetProbability A E + conditionedOffsetProbability A G := by
  unfold conditionedOffsetProbability
  rw [← add_div]
  apply div_le_div_of_nonneg_right _ (offsetProbability_nonneg A)
  have heq : (fun M => A M ∧ (E M ∨ G M)) =
      (fun M => (A M ∧ E M) ∨ (A M ∧ G M)) := by
    funext M
    exact propext and_or_left
  rw [heq]
  exact offsetProbability_or_le _ _

theorem offsetProbability_joint_eq_mul_conditioned (A E : MergedPairs F → Prop) :
    offsetProbability (fun M => A M ∧ E M) =
      offsetProbability A * conditionedOffsetProbability A E := by
  unfold conditionedOffsetProbability
  by_cases hA : offsetProbability A = 0
  · have hle := offsetProbability_mono (fun M (h : A M ∧ E M) => h.1)
    have hz : offsetProbability (fun M => A M ∧ E M) = 0 :=
      le_antisymm (hA ▸ hle) (offsetProbability_nonneg _)
    simp [hA, hz]
  · field_simp

variable {b κ : ℕ} (P : EqualityPattern b κ)
variable (a : DirectionAssignment F b κ) (bits : Bits b) (p : Point F)

theorem conditioned_badCover_four_events_le (hb : 3 ≤ b) (hκ : κ ≤ 2)
    (ha : Eligible P a) :
    conditionedOffsetProbability (Aligned P a bits p) (AdmissibleBadCover P a bits p) ≤
      conditionedOffsetProbability (Aligned P a bits p)
        (FourEvents.UnusedPrecoverage P a bits p) +
      conditionedOffsetProbability (Aligned P a bits p)
        (fun M => Admissible P a bits p M ∧ FourEvents.UsedPairExtra P a bits M) +
      conditionedOffsetProbability (Aligned P a bits p)
        (fun M => Admissible P a bits p M ∧
          FourEvents.ForbiddenCollinearTriple P a bits p M) +
      conditionedOffsetProbability (Aligned P a bits p)
        (FourEvents.UnusedNoncollinearTriple P a bits) := by
  let E₁ := FourEvents.UnusedPrecoverage P a bits p
  let E₂ := fun M => Admissible P a bits p M ∧ FourEvents.UsedPairExtra P a bits M
  let E₃ := fun M => Admissible P a bits p M ∧
    FourEvents.ForbiddenCollinearTriple P a bits p M
  let E₄ := FourEvents.UnusedNoncollinearTriple P a bits
  have hsub : ∀ M, AdmissibleBadCover P a bits p M →
      E₁ M ∨ E₂ M ∨ E₃ M ∨ E₄ M := by
    intro M hM
    rcases FourEvents.admissibleBadCover_four_events P a bits p M hb hκ ha hM with
      h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨hM.1, h⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨hM.1, h⟩))
    · exact Or.inr (Or.inr (Or.inr h))
  have h₁ := conditionedOffsetProbability_or_le (Aligned P a bits p) E₁
    (fun M => E₂ M ∨ E₃ M ∨ E₄ M)
  have h₂ := conditionedOffsetProbability_or_le (Aligned P a bits p) E₂
    (fun M => E₃ M ∨ E₄ M)
  have h₃ := conditionedOffsetProbability_or_le (Aligned P a bits p) E₃ E₄
  have hm := conditionedOffsetProbability_mono (Aligned P a bits p) hsub
  change conditionedOffsetProbability (Aligned P a bits p) (AdmissibleBadCover P a bits p) ≤
    conditionedOffsetProbability (Aligned P a bits p) E₁ +
    conditionedOffsetProbability (Aligned P a bits p) E₂ +
    conditionedOffsetProbability (Aligned P a bits p) E₃ +
    conditionedOffsetProbability (Aligned P a bits p) E₄
  linarith

theorem aligned_badCover_four_events_le (hb : 3 ≤ b) (hκ : κ ≤ 2)
    (ha : Eligible P a) :
    offsetProbability (fun M => Aligned P a bits p M ∧ AdmissibleBadCover P a bits p M) ≤
      offsetProbability (fun M => Aligned P a bits p M ∧
        FourEvents.UnusedPrecoverage P a bits p M) +
      offsetProbability (fun M => Aligned P a bits p M ∧
        (Admissible P a bits p M ∧ FourEvents.UsedPairExtra P a bits M)) +
      offsetProbability (fun M => Aligned P a bits p M ∧
        (Admissible P a bits p M ∧ FourEvents.ForbiddenCollinearTriple P a bits p M)) +
      offsetProbability (fun M => Aligned P a bits p M ∧
        FourEvents.UnusedNoncollinearTriple P a bits M) := by
  simp_rw [offsetProbability_joint_eq_mul_conditioned]
  simpa only [mul_add] using mul_le_mul_of_nonneg_left
    (conditioned_badCover_four_events_le P a bits p hb hκ ha)
    (offsetProbability_nonneg (Aligned P a bits p))

end
end Balanced.Local.UnusedOffsetProbability

end OAI
