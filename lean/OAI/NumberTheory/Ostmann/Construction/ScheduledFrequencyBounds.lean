import OAI.NumberTheory.Ostmann.Construction.ScheduledFrequencyHistory
import OAI.NumberTheory.Ostmann.Construction.TransferRoundedCutoffs
import OAI.NumberTheory.Ostmann.Construction.FinalHistoryCount

namespace OAI

/-! # The concrete rounded frequency family and its finite counting cost -/

namespace Ostmann

open scoped BigOperators Classical

theorem transferErrorScale_monotone (Δ m : ℝ) (hΔ : 0 ≤ Δ) : Monotone (transferErrorScale Δ m) := by
  apply monotone_nat_of_le_succ
  intro n
  have h2 : 0 ≤ (2 : ℝ) ^ n * Δ := mul_nonneg (by positivity) hΔ
  have h4 : 0 ≤ (4 : ℝ) ^ n * Real.sqrt m := mul_nonneg (by positivity) (Real.sqrt_nonneg m)
  simp only [transferErrorScale, pow_succ]
  nlinarith

theorem naturalTransferCutoff_monotone (Δ m : ℝ) (hΔ : 0 ≤ Δ) :
    Monotone (naturalTransferCutoff Δ m) := by
  intro a b hab
  exact Nat.floor_le_floor (Real.exp_le_exp.mpr (transferErrorScale_monotone Δ m hΔ hab))

theorem transferFrequencyRange_mono : Monotone transferFrequencyRange := by
  intro a b hab s hs
  exact (mem_transferFrequencyRange b s).mpr (((mem_transferFrequencyRange a s).mp hs).trans hab)

theorem scheduledFrequencyIndex_card_le (V : ℕ → ℕ) (hV : Monotone V) (n : ℕ) :
    Fintype.card (ScheduledFrequencyIndex V n) ≤
      (transferFrequencyRange (V n)).card ^ (2 ^ (n + 1) - 1) := by
  induction n with
  | zero =>
    have he : ScheduledFrequencyIndex V 0 ≃ transferFrequencyRange (V 0) := Equiv.refl _
    have hc := Fintype.card_congr he
    simpa only [Fintype.card_coe, Nat.zero_add, pow_one, Nat.reducePow, Nat.reduceSub] using hc.le
  | succ n ih =>
    have hc := Finset.card_le_card (transferFrequencyRange_mono (hV (Nat.le_succ n)))
    have hh := ih.trans (Nat.pow_le_pow_left hc (2 ^ (n + 1) - 1))
    have he : ScheduledFrequencyIndex V (n + 1) ≃
        (transferFrequencyRange (V (n + 1))) × (ScheduledFrequencyIndex V n × ScheduledFrequencyIndex V n) :=
      Equiv.refl _
    have hcard := Fintype.card_congr he
    simp only [Fintype.card_prod, Fintype.card_coe] at hcard
    rw [hcard]
    calc
      _ ≤ (transferFrequencyRange (V (n + 1))).card *
          ((transferFrequencyRange (V (n + 1))).card ^ (2 ^ (n + 1) - 1) *
           (transferFrequencyRange (V (n + 1))).card ^ (2 ^ (n + 1) - 1)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul hh hh)
      _ = _ := by
        rw [← pow_add, ← pow_succ']
        congr 1
        have hp : 1 ≤ 2 ^ (n + 1) := Nat.one_le_two_pow
        rw [pow_succ]
        omega

theorem scheduledFrequencyIndex_pair_card_bound (V : ℕ → ℕ) (hV : Monotone V)
    (n : ℕ) (C m : ℝ) (hS : ((transferFrequencyRange (V n)).card : ℝ) ≤ Real.exp (C * m)) :
    (Fintype.card (ScheduledFrequencyIndex V n) : ℝ) ^ 2 ≤
      Real.exp ((2 * (2 ^ (n + 1) - 1 : ℕ) : ℝ) * C * m) := by
  have hc : Fintype.card (ScheduledFrequencyIndex V n) ≤
      Fintype.card (FrequencyTree (transferFrequencyRange (V n)) n) := by
    rw [card_frequencyTree, Fintype.card_coe]
    exact scheduledFrequencyIndex_card_le V hV n
  exact (pow_le_pow_left₀ (by positivity) (by exact_mod_cast hc) 2).trans
    (frequency_history_pair_card_bound (transferFrequencyRange (V n)) n C m hS)

end Ostmann

end OAI
