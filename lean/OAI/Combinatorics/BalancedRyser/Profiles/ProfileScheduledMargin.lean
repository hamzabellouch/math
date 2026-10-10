import OAI.Combinatorics.BalancedRyser.Profiles.ProfileClassMargin
import OAI.Combinatorics.BalancedRyser.Profiles.ProfileScheduledMarks

namespace OAI

noncomputable section
attribute [local instance] Classical.propDecidable
open Filter MeasureTheory
open scoped Topology BigOperators

namespace Balanced.ProfileScheduledMargin

open ConditionalOrderVariance ProfileScheduledMarks

universe u

def threshold (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem threshold_pos (n : ℕ) : 0 < threshold n := by unfold threshold; positivity

theorem threshold_antitone : Antitone threshold := by
  intro n m hnm
  apply one_div_le_one_div_of_le (by positivity : (0 : ℝ) < (n : ℝ) + 1)
  exact_mod_cast Nat.add_le_add_right hnm 1

def sourceTest : ProfileClassMargin.Test.{u} := fun n F _ _ _ D C =>
  normalizedMean (F := F) D C (threshold n) (threshold n)

theorem sourceTest_mono (F : Type u) [Field F] [Fintype F] [DecidableEq F]
    (D C : Finset (Line F)) : Monotone (fun n => sourceTest n F D C) := by
  intro n m hnm
  exact normalizedMean_antitone D C (threshold_antitone hnm) (threshold_antitone hnm)

theorem exists_source_mean_margin
    (k : ℕ) (A : ProfileClass.{u}) (hvalid : ProfileClassValid k A)
    (hgap : ∃ a : ℝ, 0 < a ∧ ProfileClassSizeGap a A)
    (hvisible : ProfileVisibleExcess A)
    (hlower : ProfileClassMargin.LimitLowerBound A sourceTest) :
    ∃ n : ℕ, ∃ ξ : ℝ, 0 < ξ ∧ ∃ N : ℕ,
      ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F]
        (D C : Finset (Line F)), A F D C → N ≤ Fintype.card F →
        (C.card : ℝ) + ξ * (Fintype.card F : ℝ) ≤
          𝔼 p : OrderPair D C,
            (sourceMarkCount D C (threshold n) (threshold n) p : ℝ) := by
  obtain ⟨n, ξ, hξ, N, hN⟩ := ProfileClassMargin.exists_uniform_margin k A hvalid hgap
    hvisible sourceTest (fun F _ _ _ D C _ => sourceTest_mono F D C) hlower
  refine ⟨n, ξ, hξ, N, ?_⟩
  intro F _ _ _ D C hA hq
  have hqR : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos (α := F)
  have h := (le_div_iff₀ hqR).mp (hN F D C hA hq)
  simpa only [add_mul, div_mul_cancel₀ _ hqR.ne'] using h

variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]

def tailProbability (D C : Finset (Line F)) (η ε ξ : ℝ) : ℝ :=
  𝔼 p : OrderPair D C,
    if (C.card : ℝ) + ξ * (Fintype.card F : ℝ) / 2 ≤
      (sourceMarkCount D C η ε p : ℝ) then 1 else 0

theorem tailProbability_ge (k : ℕ) (hk : 1 ≤ k)
    (D C : Finset (Line F)) (hp : IsProfilePair k D C)
    (η ε ξ : ℝ) (hξ : 0 ≤ ξ)
    (hmean : (C.card : ℝ) + ξ * (Fintype.card F : ℝ) ≤
      𝔼 p : OrderPair D C, (sourceMarkCount D C η ε p : ℝ)) :
    ξ / (4 * (k : ℝ)) ≤ tailProbability D C η ε ξ := by
  let : MeasurableSpace (OrderPair D C) := ⊤
  have hkR : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  have hq : (1 : ℝ) ≤ Fintype.card F := by exact_mod_cast Fintype.card_pos (α := F)
  have hD : D.card = k * (Fintype.card F + 1) := profile_deletionSet_card k D hp.1
  have hDpos : 0 < D.card := by rw [hD]; positivity
  have hDr : (D.card : ℝ) = (k : ℝ) * ((Fintype.card F : ℝ) + 1) := by
    exact_mod_cast hD
  have ht := ProfileMarkedOrders.positive_mark_tail_of_mean_margin D C
    (ID D C) (JD D C) (zD D) (IC D C) (JC D C) (zC C)
    η ε (ξ * Fintype.card F) hDpos (mul_nonneg hξ (by positivity)) hmean
  have hprob : (ProfileMarkedOrders.orderLaw D C).toMeasure.real
      {p | (C.card : ℝ) + ξ * (Fintype.card F : ℝ) / 2 ≤
        (sourceMarkCount D C η ε p : ℝ)} = tailProbability D C η ε ξ := by
    exact ProfileMarkedOrders.real_uniform_event Finset.univ Finset.univ_nonempty _
  change ξ * (Fintype.card F : ℝ) / (2 * D.card) ≤
    (ProfileMarkedOrders.orderLaw D C).toMeasure.real
      {p | (C.card : ℝ) + ξ * (Fintype.card F : ℝ) / 2 ≤
        (sourceMarkCount D C η ε p : ℝ)} at ht
  rw [hprob] at ht
  apply le_trans _ ht
  apply (div_le_div_iff₀ (by positivity : 0 < 4 * (k : ℝ))
    (by exact_mod_cast Nat.mul_pos (by omega : 0 < 2) hDpos)).mpr
  have hbound : (D.card : ℝ) ≤ 2 * (k : ℝ) * Fintype.card F := by
    rw [hDr]
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hbound hξ]

theorem exists_uniform_positive_tail
    (k : ℕ) (hk : 1 ≤ k) (A : ProfileClass.{u})
    (hvalid : ProfileClassValid k A)
    (hgap : ∃ a : ℝ, 0 < a ∧ ProfileClassSizeGap a A)
    (hvisible : ProfileVisibleExcess A)
    (hlower : ProfileClassMargin.LimitLowerBound A sourceTest) :
    ∃ n : ℕ, ∃ ξ : ℝ, 0 < ξ ∧ ∃ N : ℕ,
      ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F]
        (D C : Finset (Line F)), A F D C → N ≤ Fintype.card F →
        ξ / (4 * (k : ℝ)) ≤ tailProbability D C (threshold n) (threshold n) ξ := by
  obtain ⟨n, ξ, hξ, N, hN⟩ := exists_source_mean_margin k A hvalid hgap hvisible hlower
  refine ⟨n, ξ, hξ, N, ?_⟩
  intro F _ _ _ D C hA hq
  exact tailProbability_ge k hk D C (hvalid F D C hA) _ _ ξ hξ.le (hN F D C hA hq)

end Balanced.ProfileScheduledMargin

end

end OAI
