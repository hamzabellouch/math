import OAI.Combinatorics.BalancedRyser.Local.LocalTwoReuseAssembly

namespace OAI

namespace Balanced.Local.TwoReuseAssembly
noncomputable section
open scoped BigOperators Classical
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
omit [Field F] [DecidableEq F] in
theorem sum_allTokensDistinct_eq {b κ : ℕ}
    (f : DirectionAssignment F b κ → ℝ) :
    (∑ a : DirectionAssignment F b κ, if AllTokensDistinct a then f a else 0) =
      ∑ e : DirectionToken b κ ↪ Direction F, f (tokenInjectionEquiv F b κ e).1 := by
  calc
    _ = ∑ a ∈ (Finset.univ.filter (fun a : DirectionAssignment F b κ => AllTokensDistinct a)), f a := by
      rw [Finset.sum_filter]
    _ = ∑ a : {a : DirectionAssignment F b κ // AllTokensDistinct a}, f a.1 := by
      exact Finset.sum_subtype _ (by simp) _
    _ = _ := (Equiv.sum_comp (tokenInjectionEquiv F b κ) (fun a => f a.1)).symm

theorem injective_conditional_sum_le_of_embedding_sum {b : ℕ}
    (P : EqualityPattern b 2) (bits : Bits b) (p : Point F)
    (hb : 1 ≤ b) (C : ℝ) (hC : 0 ≤ C)
    (hbound : (∑ e : DirectionToken b 2 ↪ Direction F,
      conditionedOffsetProbability (Aligned P (tokenInjectionEquiv F b 2 e).1 bits p)
        (AdmissibleBadCover P (tokenInjectionEquiv F b 2 e).1 bits p)) ≤
      (Fintype.card (DirectionToken b 2 ↪ Direction F) : ℝ) *
        (C * (b : ℝ) ^ 3 / Fintype.card F)) :
    (∑ a : DirectionAssignment F b 2,
      if AllTokensDistinct a then conditionedOffsetProbability
        (Aligned P a bits p) (AdmissibleBadCover P a bits p) else 0) ≤
      ((Fintype.card F + 1 : ℕ) : ℝ) ^ (5 * b - 2) *
        (C * (b : ℝ) ^ 3 / Fintype.card F) := by
  rw [sum_allTokensDistinct_eq]
  apply hbound.trans
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact_mod_cast card_token_injections_two_le (F := F) hb
theorem sum_le_card_mul_of_mean_le {I : Type*} [Fintype I]
    (f : I → ℝ) (B : ℝ) (h : (∑ i, f i) / Fintype.card I ≤ B) :
    (∑ i, f i) ≤ (Fintype.card I : ℝ) * B := by
  by_cases hc : Fintype.card I = 0
  · have : IsEmpty I := Fintype.card_eq_zero_iff.mp hc
    simp
  · have hp : (0 : ℝ) < Fintype.card I := by
      exact_mod_cast Nat.pos_of_ne_zero hc
    simpa [mul_comm] using (div_le_iff₀ hp).mp h

theorem injective_conditional_sum_le_of_embedding_mean {b : ℕ}
    (P : EqualityPattern b 2) (bits : Bits b) (p : Point F)
    (hb : 1 ≤ b) (C : ℝ) (hC : 0 ≤ C)
    (hbound : (∑ e : DirectionToken b 2 ↪ Direction F,
      conditionedOffsetProbability (Aligned P (tokenInjectionEquiv F b 2 e).1 bits p)
        (AdmissibleBadCover P (tokenInjectionEquiv F b 2 e).1 bits p)) /
        Fintype.card (DirectionToken b 2 ↪ Direction F) ≤
      C * (b : ℝ) ^ 3 / Fintype.card F) :
    (∑ a : DirectionAssignment F b 2,
      if AllTokensDistinct a then conditionedOffsetProbability
        (Aligned P a bits p) (AdmissibleBadCover P a bits p) else 0) ≤
      ((Fintype.card F + 1 : ℕ) : ℝ) ^ (5 * b - 2) *
        (C * (b : ℝ) ^ 3 / Fintype.card F) :=
  injective_conditional_sum_le_of_embedding_sum P bits p hb C hC
    (sum_le_card_mul_of_mean_le _ _ hbound)

universe u

def InjectiveTwoReuseMeanEstimate : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ q₀ : ℕ,
    ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
      q₀ ≤ Fintype.card F → ∀ b : ℕ, 3 ≤ b → b ≤ logBudget F →
      ∀ (P : EqualityPattern b 2) (bits : Bits b) (p : Point F),
        (∑ e : DirectionToken b 2 ↪ Direction F,
          conditionedOffsetProbability
            (Aligned P (tokenInjectionEquiv F b 2 e).1 bits p)
            (AdmissibleBadCover P (tokenInjectionEquiv F b 2 e).1 bits p)) /
          Fintype.card (DirectionToken b 2 ↪ Direction F) ≤
            C * (b : ℝ) ^ 3 / Fintype.card F

theorem pencilTwoReuses_of_alignment_and_injective_mean
    (halign : AlignmentNormalizationResult.{u})
    (hmean : InjectiveTwoReuseMeanEstimate.{u}) : PencilTwoReusesResult.{u} := by
  apply pencilTwoReuses_of_alignment_and_injective halign
  obtain ⟨C, hC, q₀, hbound⟩ := hmean
  refine ⟨C, hC, q₀, ?_⟩
  intro F _ _ _ hq b hb hB P bits p
  exact injective_conditional_sum_le_of_embedding_mean P bits p (by omega) C hC.le
    (hbound F hq b hb hB P bits p)

theorem pencilTwoReuses_of_injective_mean
    (hmean : InjectiveTwoReuseMeanEstimate.{u}) : PencilTwoReusesResult.{u} :=
  pencilTwoReuses_of_alignment_and_injective_mean alignmentNormalization_proof hmean

theorem pencilTwoReuses_of_injective
    (hinjective : InjectiveTwoReuseEstimate.{u}) : PencilTwoReusesResult.{u} :=
  pencilTwoReuses_of_alignment_and_injective alignmentNormalization_proof hinjective

end
end Balanced.Local.TwoReuseAssembly

end OAI
