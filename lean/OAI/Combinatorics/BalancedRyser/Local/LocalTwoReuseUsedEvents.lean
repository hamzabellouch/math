import OAI.Combinatorics.BalancedRyser.Local.AlignedUnusedTripleBound
import OAI.Combinatorics.BalancedRyser.Local.LocalTwoReuseMean

namespace OAI

namespace Balanced.Local.TwoReuseAssembly
noncomputable section
open scoped Classical BigOperators

theorem unused_errors_le (q b : ℝ) (hq : 1 ≤ q) (hb : 1 ≤ b) :
    8 * b * (q + 1) / q ^ 2 + 384 * b ^ 3 / q ^ 2 ≤ 400 * b ^ 3 / q := by
  have hq0 : 0 < q := by linarith
  have hb0 : 0 ≤ b := by linarith
  have hb3 : 0 ≤ b ^ 3 := pow_nonneg hb0 3
  have hbb : b ≤ b ^ 3 := by nlinarith [sq_nonneg (b - 1)]
  have hfirst : 8 * b * (q + 1) ≤ 16 * b ^ 3 * q := by
    calc
      _ ≤ 8 * b ^ 3 * (q + 1) := by gcongr
      _ ≤ _ := by nlinarith [mul_nonneg hb3 (sub_nonneg.mpr hq)]
  have hlast : 384 * b ^ 3 ≤ 384 * b ^ 3 * q := by
    nlinarith [mul_nonneg hb3 (sub_nonneg.mpr hq)]
  calc
    _ = (8 * b * (q + 1) + 384 * b ^ 3) / q ^ 2 := by ring
    _ ≤ (400 * b ^ 3 * q) / q ^ 2 :=
      div_le_div_of_nonneg_right (by linarith) (sq_nonneg q)
    _ = _ := by field_simp

theorem mean_le_mean_add {I : Type*} [Fintype I]
    (f g : I → ℝ) (B : ℝ) (hB : 0 ≤ B) (h : ∀ i, f i ≤ g i + B) :
    (∑ i, f i) / Fintype.card I ≤ (∑ i, g i) / Fintype.card I + B := by
  by_cases hc : Fintype.card I = 0
  · simpa [hc] using hB
  have hcR : (Fintype.card I : ℝ) ≠ 0 := by exact_mod_cast hc
  calc
    _ ≤ (∑ i, (g i + B)) / Fintype.card I :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum (fun i _ => h i)) (Nat.cast_nonneg _)
    _ = _ := by rw [Finset.sum_add_distrib]; simp; field_simp

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def usedEventConditionalMass {b : ℕ} (P : EqualityPattern b 2)
    (a : DirectionAssignment F b 2) (bits : Bits b) (p : Point F) : ℝ :=
  conditionedOffsetProbability (Aligned P a bits p)
    (fun M => Admissible P a bits p M ∧ FourEvents.UsedPairExtra P a bits M) +
  conditionedOffsetProbability (Aligned P a bits p)
    (fun M => Admissible P a bits p M ∧ FourEvents.ForbiddenCollinearTriple P a bits p M)

def usedEventMean {b : ℕ} (P : EqualityPattern b 2) (bits : Bits b) (p : Point F) : ℝ :=
  (∑ e : DirectionToken b 2 ↪ Direction F,
    usedEventConditionalMass P (tokenInjectionEquiv F b 2 e).1 bits p) /
      Fintype.card (DirectionToken b 2 ↪ Direction F)

theorem badCover_mean_le_usedEventMean {b : ℕ} (P : EqualityPattern b 2)
    (bits : Bits b) (p : Point F) (hb : 3 ≤ b) :
    (∑ e : DirectionToken b 2 ↪ Direction F,
      conditionedOffsetProbability (Aligned P (tokenInjectionEquiv F b 2 e).1 bits p)
        (AdmissibleBadCover P (tokenInjectionEquiv F b 2 e).1 bits p)) /
      Fintype.card (DirectionToken b 2 ↪ Direction F) ≤
        usedEventMean P bits p + 400 * (b : ℝ) ^ 3 / Fintype.card F := by
  apply mean_le_mean_add _ _ _ (by positivity)
  intro e
  let a := (tokenInjectionEquiv F b 2 e).1
  have ha : Eligible P a := allTokensDistinct_eligible P a (tokenInjectionEquiv F b 2 e).2
  have h := UnusedTripleProbability.conditioned_badCover_le_used_events
    P hb (by omega) a ha bits p
  have hq : (1 : ℝ) ≤ Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hbR : (1 : ℝ) ≤ b := by exact_mod_cast (show 1 ≤ b by omega)
  have hn := unused_errors_le (Fintype.card F : ℝ) (b : ℝ) hq hbR
  change conditionedOffsetProbability (Aligned P a bits p) (AdmissibleBadCover P a bits p) ≤
    usedEventConditionalMass P a bits p + _
  unfold usedEventConditionalMass
  linarith

universe u

def InjectiveUsedEventsEstimate : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ q₀ : ℕ,
    ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
      q₀ ≤ Fintype.card F → ∀ b : ℕ, 3 ≤ b → b ≤ logBudget F →
      ∀ (P : EqualityPattern b 2) (bits : Bits b) (p : Point F),
        usedEventMean P bits p ≤ C * (b : ℝ) ^ 3 / Fintype.card F

theorem pencilTwoReuses_of_used_event_mean
    (hused : InjectiveUsedEventsEstimate.{u}) : PencilTwoReusesResult.{u} := by
  apply pencilTwoReuses_of_injective_mean
  obtain ⟨C, hC, q₀, hbound⟩ := hused
  refine ⟨C + 400, by linarith only [hC], q₀, ?_⟩
  intro F _ _ _ hq b hb hB P bits p
  have h₁ := badCover_mean_le_usedEventMean P bits p hb
  have h₂ : usedEventMean P bits p + 400 * (b : ℝ) ^ 3 / Fintype.card F ≤
      C * (b : ℝ) ^ 3 / Fintype.card F + 400 * (b : ℝ) ^ 3 / Fintype.card F :=
    add_le_add (hbound F hq b hb hB P bits p) le_rfl
  have hn : C * (b : ℝ) ^ 3 / Fintype.card F +
      400 * (b : ℝ) ^ 3 / Fintype.card F =
      (C + 400) * (b : ℝ) ^ 3 / Fintype.card F := by ring
  exact h₁.trans (h₂.trans_eq hn)

end
end Balanced.Local.TwoReuseAssembly

end OAI
