import OAI.NumberTheory.Ostmann.Arithmetic.ArithmeticPatternPriorRate
import OAI.NumberTheory.Ostmann.Construction.FinalHistoryCount

namespace OAI

/-! # The original pattern and frequency counts preserve the arithmetic error -/

namespace Ostmann
open Filter

theorem pairedFrequencyTree_card (S : Finset ℤ) (n : ℕ) :
    Fintype.card (FrequencyTree (S × S) n) = (Fintype.card (FrequencyTree S n)) ^ 2 := by
  simp only [card_frequencyTree, Fintype.card_prod, pow_two, mul_pow]

theorem movingPattern_frequency_error_rate (n k : ℕ) (hk : 0 < k)
    (Cprior Cfreq α β : ℝ) (hCprior : 1 ≤ Cprior) (hCfreq : 0 ≤ Cfreq)
    (hα : 0 < α) (hβα : β < α) :
    ∀ᶠ L : ℝ in atTop, ∀ S : Finset ℤ,
      (S.card : ℝ) ≤ Real.exp (Cfreq * spectatorBulkCount k L) →
      ((2 : ℝ) ^ ((4 * n * 2 ^ n) ^ 2) *
        (max 2 (Real.exp (Cprior * L))) ^ (4 * n * 2 ^ n)) *
        (Fintype.card (FrequencyTree (S × S) n) : ℝ) * Real.exp (-Real.exp (α * L)) ≤
          Real.exp (-Real.exp (β * L)) := by
  let J := 4 * n * 2 ^ n
  let A : ℝ := ((J ^ 2 + J : ℕ) : ℝ) * Cprior
  let B : ℝ := (2 * (2 ^ (n + 1) - 1 : ℕ) : ℝ) * Cfreq
  let H := A + B * (k : ℝ) ^ 4
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hH : 0 ≤ H := by dsimp only [H]; positivity
  filter_upwards [arithmetic_exponent_absorption 0 α β H 1 0 hα hα hβα (by norm_num),
    eventually_ge_atTop (1 : ℝ)] with L hrate hL S hS
  have hL0 : 0 ≤ L := by linarith
  have hp := movingPattern_total_cost_le_exp n Cprior L hCprior hL
  have hc := frequency_history_pair_card_bound S n Cfreq (spectatorBulkCount k L) hS
  have hc' : (Fintype.card (FrequencyTree (S × S) n) : ℝ) ≤
      Real.exp (B * (k : ℝ) ^ 4 * L) := by
    rw [pairedFrequencyTree_card, Nat.cast_pow]
    apply hc.trans
    apply Real.exp_le_exp.mpr
    have hm := mul_le_mul_of_nonneg_left (spectatorBulkCount_upper k L hL0) hB
    exact hm.trans_eq (by ring)
  have hprod := mul_le_mul hp hc' (Nat.cast_nonneg _) (Real.exp_nonneg _)
  have hexp : ((2 : ℝ) ^ ((4 * n * 2 ^ n) ^ 2) *
      (max 2 (Real.exp (Cprior * L))) ^ (4 * n * 2 ^ n)) *
      (Fintype.card (FrequencyTree (S × S) n) : ℝ) ≤ Real.exp (H * L) := by
    apply hprod.trans_eq
    rw [← Real.exp_add]
    congr 1
    dsimp only [H, A, J]
    ring
  apply (mul_le_mul_of_nonneg_right hexp (Real.exp_nonneg _)).trans
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  simp only [pow_zero, mul_one, zero_mul, Real.exp_zero, one_mul] at hrate
  linarith

/-- All three errors in the original-prior norm bound fit the final common
scale after the exact equality-pattern and two-history sums. -/
theorem movingPattern_three_errors_rate (n k : ℕ) (hk : 0 < k)
    (Cprior Cfreq : ℝ) (hCprior : 1 ≤ Cprior) (hCfreq : 0 ≤ Cfreq) :
    ∀ᶠ L : ℝ in atTop, ∀ S : Finset ℤ,
      (S.card : ℝ) ≤ Real.exp (Cfreq * spectatorBulkCount k L) →
      ((2 : ℝ) ^ ((4 * n * 2 ^ n) ^ 2) *
        (max 2 (Real.exp (Cprior * L))) ^ (4 * n * 2 ^ n)) *
        (Fintype.card (FrequencyTree (S × S) n) : ℝ) *
          (Real.exp (-Real.exp ((125 / 100000 : ℝ) * L)) +
            2 * Real.exp (-Real.exp ((2 / 1000 : ℝ) * L))) ≤
        3 * Real.exp (-Real.exp ((12 / 10000 : ℝ) * L)) := by
  filter_upwards [movingPattern_frequency_error_rate n k hk Cprior Cfreq
      (125 / 100000) (12 / 10000) hCprior hCfreq (by norm_num) (by norm_num),
    movingPattern_frequency_error_rate n k hk Cprior Cfreq
      (2 / 1000) (12 / 10000) hCprior hCfreq (by norm_num) (by norm_num)]
    with L hfirst hsecond S hS
  have h := add_le_add (hfirst S hS) (mul_le_mul_of_nonneg_left (hsecond S hS)
    (by norm_num : (0 : ℝ) ≤ 2))
  nlinarith only [h]

/-- The internal-prime comparison contributes one further error of the same
scale. All four errors survive both finite sums with a common saving. -/
theorem movingPattern_four_errors_rate (n k : ℕ) (hk : 0 < k)
    (Cprior Cfreq : ℝ) (hCprior : 1 ≤ Cprior) (hCfreq : 0 ≤ Cfreq) :
    ∀ᶠ L : ℝ in atTop, ∀ S : Finset ℤ,
      (S.card : ℝ) ≤ Real.exp (Cfreq * spectatorBulkCount k L) →
      ((2 : ℝ) ^ ((4 * n * 2 ^ n) ^ 2) *
        (max 2 (Real.exp (Cprior * L))) ^ (4 * n * 2 ^ n)) *
        (Fintype.card (FrequencyTree (S × S) n) : ℝ) *
          (Real.exp (-Real.exp ((125 / 100000 : ℝ) * L)) +
            3 * Real.exp (-Real.exp ((2 / 1000 : ℝ) * L))) ≤
        4 * Real.exp (-Real.exp ((12 / 10000 : ℝ) * L)) := by
  filter_upwards [movingPattern_three_errors_rate n k hk Cprior Cfreq hCprior hCfreq,
    movingPattern_frequency_error_rate n k hk Cprior Cfreq
      (2 / 1000) (12 / 10000) hCprior hCfreq (by norm_num) (by norm_num)]
    with L hthree hone S hS
  have h := add_le_add (hthree S hS) (hone S hS)
  nlinarith only [h]

/-- The literal giant comparison adds one further error to the two bulk and
one internal comparison errors. All five survive the exact finite sums. -/
theorem movingPattern_five_errors_rate (n k : ℕ) (hk : 0 < k)
    (Cprior Cfreq : ℝ) (hCprior : 1 ≤ Cprior) (hCfreq : 0 ≤ Cfreq) :
    ∀ᶠ L : ℝ in atTop, ∀ S : Finset ℤ,
      (S.card : ℝ) ≤ Real.exp (Cfreq * spectatorBulkCount k L) →
      ((2 : ℝ) ^ ((4 * n * 2 ^ n) ^ 2) *
        (max 2 (Real.exp (Cprior * L))) ^ (4 * n * 2 ^ n)) *
        (Fintype.card (FrequencyTree (S × S) n) : ℝ) *
          (Real.exp (-Real.exp ((125 / 100000 : ℝ) * L)) +
            4 * Real.exp (-Real.exp ((2 / 1000 : ℝ) * L))) ≤
        5 * Real.exp (-Real.exp ((12 / 10000 : ℝ) * L)) := by
  filter_upwards [movingPattern_four_errors_rate n k hk Cprior Cfreq hCprior hCfreq,
    movingPattern_frequency_error_rate n k hk Cprior Cfreq
      (2 / 1000) (12 / 10000) hCprior hCfreq (by norm_num) (by norm_num)]
    with L hfour hone S hS
  have h := add_le_add (hfour S hS) (hone S hS)
  nlinarith only [h]

end Ostmann

end OAI
