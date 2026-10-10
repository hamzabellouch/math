import OAI.NumberTheory.Ostmann.Arithmetic.ArithmeticPatternErrorRate

namespace OAI

/-! # Full equality-pattern and frequency sums in the good-matching estimate -/

namespace Ostmann
open Filter
open scoped Classical BigOperators

/-- The signed gain can be chosen before the local quartet tolerance. This
amount absorbs every original pattern and paired-frequency count. -/
def goodPatternGain (n : ℕ) (Cprior Cfreq gain : ℝ) : ℝ :=
  2 * (((4 * n * 2 ^ n) ^ 2 + 4 * n * 2 ^ n : ℕ) : ℝ) * Cprior +
    (2 * (2 ^ (n + 1) - 1 : ℕ) : ℝ) * Cfreq + gain

theorem arithmetic_good_pattern_rate (n k : ℕ) (hk : 0 < k)
    (Cprior Cfreq gain : ℝ) (hCprior : 1 ≤ Cprior) (hCfreq : 0 ≤ Cfreq) :
    ∀ᶠ L : ℝ in atTop, let m := spectatorBulkCount k L
      ∀ S : Finset ℤ, (S.card : ℝ) ≤ Real.exp (Cfreq * m) →
      let _ := sampleSetoidFintype (Bool × MovingSampleIndex n)
      ∀ R : Setoid (Bool × MovingSampleIndex n) → FrequencyTree (S × S) n → ℂ,
      (∀ s t, ‖R s t‖ ≤
        ((2 : ℝ) ^ Fintype.card (Quotient s) *
          (Real.exp (Cprior * L)) ^ (4 * n * 2 ^ n - Fintype.card (Quotient s))) *
        (Real.exp (-goodPatternGain n Cprior Cfreq gain * m) +
          Real.exp (-Real.exp ((125 / 100000 : ℝ) * L)) +
          4 * Real.exp (-Real.exp ((2 / 1000 : ℝ) * L)))) →
      ‖∑ s, ∑ t, R s t‖ ≤ Real.exp (-gain * m) +
        5 * Real.exp (-Real.exp ((12 / 10000 : ℝ) * L)) := by
  filter_upwards [movingPattern_five_errors_rate n k hk Cprior Cfreq hCprior hCfreq,
    eventually_ge_atTop (4 : ℝ)] with L herrors hL
  dsimp only
  intro S hS R hR
  let _ := sampleSetoidFintype (Bool × MovingSampleIndex n)
  let m := spectatorBulkCount k L
  let A : ℝ := (((4 * n * 2 ^ n) ^ 2 + 4 * n * 2 ^ n : ℕ) : ℝ) * Cprior
  let B : ℝ := (2 * (2 ^ (n + 1) - 1 : ℕ) : ℝ) * Cfreq
  let cost := (2 : ℝ) ^ ((4 * n * 2 ^ n) ^ 2) *
    (max 2 (Real.exp (Cprior * L))) ^ (4 * n * 2 ^ n)
  let err := Real.exp (-Real.exp ((125 / 100000 : ℝ) * L)) +
    4 * Real.exp (-Real.exp ((2 / 1000 : ℝ) * L))
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hL0 : 0 ≤ L := by linarith
  have hkpow : (1 : ℝ) ≤ (k : ℝ) ^ 4 := one_le_pow₀ (by exact_mod_cast hk)
  have hLL : L ≤ (k : ℝ) ^ 4 * L := by nlinarith only [hkpow, hL0]
  have hhalf := spectatorBulkCount_half k L (show 4 ≤ (k : ℝ) ^ 4 * L by linarith)
  have hLm : L ≤ 2 * (m : ℝ) := by dsimp only [m]; linarith
  have hcost : cost ≤ Real.exp (2 * A * m) := by
    apply (movingPattern_total_cost_le_exp n Cprior L hCprior (by linarith)).trans
    apply Real.exp_le_exp.mpr
    change A * L ≤ 2 * A * m
    nlinarith only [hLm, hA]
  have hcard : (Fintype.card (FrequencyTree (S × S) n) : ℝ) ≤ Real.exp (B * m) := by
    rw [pairedFrequencyTree_card, Nat.cast_pow]
    exact frequency_history_pair_card_bound S n Cfreq m hS
  have hgain : cost * (Fintype.card (FrequencyTree (S × S) n) : ℝ) *
      Real.exp (-goodPatternGain n Cprior Cfreq gain * m) ≤ Real.exp (-gain * m) := by
    apply (mul_le_mul_of_nonneg_right
      (mul_le_mul hcost hcard (Nat.cast_nonneg _) (Real.exp_nonneg _)) (Real.exp_nonneg _)).trans_eq
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    dsimp only [goodPatternGain, A, B]
    ring
  have hsum : ‖∑ s, ∑ t, R s t‖ ≤
      cost * (Fintype.card (FrequencyTree (S × S) n) : ℝ) *
        (Real.exp (-goodPatternGain n Cprior Cfreq gain * m) + err) := by
    have hs (s : Setoid (Bool × MovingSampleIndex n)) :
        ‖∑ t, R s t‖ ≤
          ((Fintype.card (FrequencyTree (S × S) n) : ℝ) *
            (Real.exp (-goodPatternGain n Cprior Cfreq gain * m) + err)) *
          ((2 : ℝ) ^ Fintype.card (Quotient s) *
            (Real.exp (Cprior * L)) ^ (4 * n * 2 ^ n - Fintype.card (Quotient s))) := by
      apply (norm_sum_le_of_le _ (fun t _ => hR s t)).trans_eq
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      dsimp only [err]
      ring
    have hh := movingPattern_error_sum_le n (Real.exp (Cprior * L))
      ((Fintype.card (FrequencyTree (S × S) n) : ℝ) *
        (Real.exp (-goodPatternGain n Cprior Cfreq gain * m) + err))
      (Real.exp_nonneg _) (by dsimp only [err]; positivity) (fun s => ∑ t, R s t) hs
    exact hh.trans_eq (by dsimp only [cost]; ring)
  have he : cost * (Fintype.card (FrequencyTree (S × S) n) : ℝ) * err ≤
      5 * Real.exp (-Real.exp ((12 / 10000 : ℝ) * L)) := herrors S hS
  calc
    _ ≤ _ := hsum
    _ = cost * (Fintype.card (FrequencyTree (S × S) n) : ℝ) *
          Real.exp (-goodPatternGain n Cprior Cfreq gain * m) +
        cost * (Fintype.card (FrequencyTree (S × S) n) : ℝ) * err := by ring
    _ ≤ _ := add_le_add hgain he

end Ostmann

end OAI
