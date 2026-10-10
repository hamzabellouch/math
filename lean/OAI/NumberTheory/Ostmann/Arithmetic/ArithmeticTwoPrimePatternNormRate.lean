import OAI.NumberTheory.Ostmann.Arithmetic.ArithmeticPatternErrorRate
import OAI.NumberTheory.Ostmann.Arithmetic.PrimePatternFrequencyNormSum

namespace OAI

/-! # The full numerical norm bound with the original equality patterns -/

namespace Ostmann
open Filter
open scoped Classical BigOperators

/-- The actual pattern sum and paired frequency sum have an absolute bulk
constant. The cutoff includes the constructed bottom reserve `2 sqrt(m)`.
Only the genuine comparison errors use the full number of histories. -/
theorem arithmetic_two_prime_pattern_norm_rate (ψ : SchwartzMap ℝ ℂ) (n k : ℕ)
    (hk : 0 < k) (hn : n ≤ k) (B Cfreq Cprior ε : ℝ)
    (hCfreq : 0 ≤ Cfreq) (hCprior : 1 ≤ Cprior) (hε : 0 < ε)
    (hdepth : 8 * (Cprior + 1) ≤ (k : ℝ) ^ 3) :
    ∀ᶠ L : ℝ in atTop, let m := spectatorBulkCount k L
      ∃ D : ℝ, 0 ≤ D ∧
        (∀ q : ℕ, q ≠ 0 → (q : ℝ) ≤ Real.exp (2 * Cfreq * m) →
          (q.divisors.card : ℝ) ≤ D) ∧
        ∀ (S : Finset ℤ) (N V : ℕ) (Δ err : ℝ),
        (S.card : ℝ) ≤ Real.exp (Cfreq * m) →
        (∀ s ∈ S, s ≠ 0 ∧ s.natAbs ≤ N) →
        (N : ℝ) ≤ Real.exp (Cfreq * m) →
        (V : ℝ) ≤ Real.exp (Δ + Real.sqrt (4 * m)) →
        0 ≤ err → err ≤ Real.exp (-Real.exp ((125 / 100000 : ℝ) * L)) +
          3 * Real.exp (-Real.exp ((2 / 1000 : ℝ) * L)) →
        let _ := sampleSetoidFintype (Bool × MovingSampleIndex n)
        let K := ((SchwartzMap.seminorm ℝ 0 0 ψ / Real.sqrt (Real.exp Δ)) ^ (2 ^ n) *
            B ^ (2 ^ n - 1)) ^ 2 *
          ((2 : ℝ) ^ (2 ^ n * m) * 4 * 3 ^ (2 ^ n * m)) * 2 ^ (2 ^ n * m)
        ∀ R : Setoid (Bool × MovingSampleIndex n) → FrequencyTree (S × S) n → ℂ,
        (∀ s t, ‖R s t‖ ≤
          ((4 : ℝ) ^ Fintype.card (Quotient s) *
            (Real.exp (Cprior * L)) ^ (4 * n * 2 ^ n - Fintype.card (Quotient s))) *
          (err + K * (frequencyLeafWeight (pairedFrequencyLeaf S V) n t *
            ((frequencySplitList S n t).map (pairFrequencySupportBound D)).prod))) →
        ‖∑ s, ∑ t, R s t‖ ≤
          Real.exp ((2 ^ n : ℕ) * Δ + (Real.log 12 + 1) * (2 ^ n : ℕ) * m + ε * m) +
            4 * Real.exp (-Real.exp ((12 / 10000 : ℝ) * L)) := by
  have hCplus : 1 ≤ Cprior + 1 := by linarith
  filter_upwards [arithmetic_prime_pattern_budget_rate ψ n k hk hn B Cfreq (Cprior + 1) ε
      hCfreq hCplus hε hdepth,
    movingPattern_four_errors_rate n k hk (Cprior + 1) Cfreq hCplus hCfreq,
    eventually_ge_atTop (2 : ℝ)] with L hbudget herrors hL
  dsimp only
  obtain ⟨D, hD, hdiv, hbudget⟩ := hbudget
  refine ⟨D, hD, hdiv, ?_⟩
  intro S N V Δ err hcard hS hN hV herr herrbound R hR
  have hdivN : ∀ q : ℕ, q ≠ 0 → q ≤ N ^ 2 → (q.divisors.card : ℝ) ≤ D := by
    intro q hq hqN
    apply hdiv q hq
    calc
      (q : ℝ) ≤ (N : ℝ) ^ 2 := by exact_mod_cast hqN
      _ ≤ (Real.exp (Cfreq * spectatorBulkCount k L)) ^ 2 :=
        pow_le_pow_left₀ (Nat.cast_nonneg N) hN 2
      _ = Real.exp (2 * Cfreq * spectatorBulkCount k L) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
  have hexp : (4 : ℝ) ≤ Real.exp ((Cprior + 1) * L) := by
    have hCL := mul_le_mul hCplus hL (by norm_num : (0 : ℝ) ≤ 2) (by linarith)
    have hCL' := mul_le_mul_of_nonneg_right hCprior (by linarith : 0 ≤ L)
    linarith [Real.add_one_le_exp ((Cprior + 1) * L)]
  have hmono : max 4 (Real.exp (Cprior * L)) ≤ max 2 (Real.exp ((Cprior + 1) * L)) := by
    apply max_le
    · exact hexp.trans (le_max_right _ _)
    · exact (Real.exp_le_exp.mpr (by linarith)).trans (le_max_right _ _)
  have hpriorcost :
      (2 : ℝ) ^ ((4 * n * 2 ^ n) ^ 2) * (max 4 (Real.exp (Cprior * L))) ^ (4 * n * 2 ^ n) ≤
      (2 : ℝ) ^ ((4 * n * 2 ^ n) ^ 2) * (max 2 (Real.exp ((Cprior + 1) * L))) ^ (4 * n * 2 ^ n) :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hmono _) (by positivity)
  have hsum := prime_pattern_frequency_norm_sum_le S n N V D (Real.exp (Cprior * L))
    (((SchwartzMap.seminorm ℝ 0 0 ψ / Real.sqrt (Real.exp Δ)) ^ (2 ^ n) *
      B ^ (2 ^ n - 1)) ^ 2 *
      ((2 : ℝ) ^ (2 ^ n * spectatorBulkCount k L) * 4 * 3 ^ (2 ^ n * spectatorBulkCount k L)) *
        2 ^ (2 ^ n * spectatorBulkCount k L)) err hD (Real.exp_nonneg _) (by positivity)
      herr hS hdivN R hR
  have hcost := (mul_le_mul_of_nonneg_right hpriorcost (by positivity)).trans (hbudget N V Δ hN hV)
  have he := (mul_le_mul_of_nonneg_left herrbound
    (show 0 ≤ ((2 : ℝ) ^ ((4 * n * 2 ^ n) ^ 2) *
      (max 4 (Real.exp (Cprior * L))) ^ (4 * n * 2 ^ n)) *
      (Fintype.card (FrequencyTree (S × S) n) : ℝ) by positivity)).trans
      ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpriorcost
        (Nat.cast_nonneg _)) (by positivity)).trans (herrors S hcard))
  apply hsum.trans
  nlinarith only [hcost, he]

/-- The actual pattern sum and paired frequency sum have an absolute bulk
constant. The cutoff includes the constructed bottom reserve `2 sqrt(m)`.
The fifth error is the literal giant comparison; only comparison errors use the full number of histories. -/
theorem arithmetic_two_prime_original_pattern_norm_rate (ψ : SchwartzMap ℝ ℂ) (n k : ℕ)
    (hk : 0 < k) (hn : n ≤ k) (B Cfreq Cprior ε : ℝ)
    (hCfreq : 0 ≤ Cfreq) (hCprior : 1 ≤ Cprior) (hε : 0 < ε)
    (hdepth : 8 * (Cprior + 1) ≤ (k : ℝ) ^ 3) :
    ∀ᶠ L : ℝ in atTop, let m := spectatorBulkCount k L
      ∃ D : ℝ, 0 ≤ D ∧
        (∀ q : ℕ, q ≠ 0 → (q : ℝ) ≤ Real.exp (2 * Cfreq * m) →
          (q.divisors.card : ℝ) ≤ D) ∧
        ∀ (S : Finset ℤ) (N V : ℕ) (Δ err : ℝ),
        (S.card : ℝ) ≤ Real.exp (Cfreq * m) →
        (∀ s ∈ S, s ≠ 0 ∧ s.natAbs ≤ N) →
        (N : ℝ) ≤ Real.exp (Cfreq * m) →
        (V : ℝ) ≤ Real.exp (Δ + Real.sqrt (4 * m)) →
        0 ≤ err → err ≤ Real.exp (-Real.exp ((125 / 100000 : ℝ) * L)) +
          4 * Real.exp (-Real.exp ((2 / 1000 : ℝ) * L)) →
        let _ := sampleSetoidFintype (Bool × MovingSampleIndex n)
        let K := ((SchwartzMap.seminorm ℝ 0 0 ψ / Real.sqrt (Real.exp Δ)) ^ (2 ^ n) *
            B ^ (2 ^ n - 1)) ^ 2 *
          ((2 : ℝ) ^ (2 ^ n * m) * 4 * 3 ^ (2 ^ n * m)) * 2 ^ (2 ^ n * m)
        ∀ R : Setoid (Bool × MovingSampleIndex n) → FrequencyTree (S × S) n → ℂ,
        (∀ s t, ‖R s t‖ ≤
          ((4 : ℝ) ^ Fintype.card (Quotient s) *
            (Real.exp (Cprior * L)) ^ (4 * n * 2 ^ n - Fintype.card (Quotient s))) *
          (err + K * (frequencyLeafWeight (pairedFrequencyLeaf S V) n t *
            ((frequencySplitList S n t).map (pairFrequencySupportBound D)).prod))) →
        ‖∑ s, ∑ t, R s t‖ ≤
          Real.exp ((2 ^ n : ℕ) * Δ + (Real.log 12 + 1) * (2 ^ n : ℕ) * m + ε * m) +
            5 * Real.exp (-Real.exp ((12 / 10000 : ℝ) * L)) := by
  have hCplus : 1 ≤ Cprior + 1 := by linarith
  filter_upwards [arithmetic_prime_pattern_budget_rate ψ n k hk hn B Cfreq (Cprior + 1) ε
      hCfreq hCplus hε hdepth,
    movingPattern_five_errors_rate n k hk (Cprior + 1) Cfreq hCplus hCfreq,
    eventually_ge_atTop (2 : ℝ)] with L hbudget herrors hL
  dsimp only
  obtain ⟨D, hD, hdiv, hbudget⟩ := hbudget
  refine ⟨D, hD, hdiv, ?_⟩
  intro S N V Δ err hcard hS hN hV herr herrbound R hR
  have hdivN : ∀ q : ℕ, q ≠ 0 → q ≤ N ^ 2 → (q.divisors.card : ℝ) ≤ D := by
    intro q hq hqN
    apply hdiv q hq
    calc
      (q : ℝ) ≤ (N : ℝ) ^ 2 := by exact_mod_cast hqN
      _ ≤ (Real.exp (Cfreq * spectatorBulkCount k L)) ^ 2 :=
        pow_le_pow_left₀ (Nat.cast_nonneg N) hN 2
      _ = Real.exp (2 * Cfreq * spectatorBulkCount k L) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
  have hexp : (4 : ℝ) ≤ Real.exp ((Cprior + 1) * L) := by
    have hCL := mul_le_mul hCplus hL (by norm_num : (0 : ℝ) ≤ 2) (by linarith)
    have hCL' := mul_le_mul_of_nonneg_right hCprior (by linarith : 0 ≤ L)
    linarith [Real.add_one_le_exp ((Cprior + 1) * L)]
  have hmono : max 4 (Real.exp (Cprior * L)) ≤ max 2 (Real.exp ((Cprior + 1) * L)) := by
    apply max_le
    · exact hexp.trans (le_max_right _ _)
    · exact (Real.exp_le_exp.mpr (by linarith)).trans (le_max_right _ _)
  have hpriorcost :
      (2 : ℝ) ^ ((4 * n * 2 ^ n) ^ 2) * (max 4 (Real.exp (Cprior * L))) ^ (4 * n * 2 ^ n) ≤
      (2 : ℝ) ^ ((4 * n * 2 ^ n) ^ 2) * (max 2 (Real.exp ((Cprior + 1) * L))) ^ (4 * n * 2 ^ n) :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hmono _) (by positivity)
  have hsum := prime_pattern_frequency_norm_sum_le S n N V D (Real.exp (Cprior * L))
    (((SchwartzMap.seminorm ℝ 0 0 ψ / Real.sqrt (Real.exp Δ)) ^ (2 ^ n) *
      B ^ (2 ^ n - 1)) ^ 2 *
      ((2 : ℝ) ^ (2 ^ n * spectatorBulkCount k L) * 4 * 3 ^ (2 ^ n * spectatorBulkCount k L)) *
        2 ^ (2 ^ n * spectatorBulkCount k L)) err hD (Real.exp_nonneg _) (by positivity)
      herr hS hdivN R hR
  have hcost := (mul_le_mul_of_nonneg_right hpriorcost (by positivity)).trans (hbudget N V Δ hN hV)
  have he := (mul_le_mul_of_nonneg_left herrbound
    (show 0 ≤ ((2 : ℝ) ^ ((4 * n * 2 ^ n) ^ 2) *
      (max 4 (Real.exp (Cprior * L))) ^ (4 * n * 2 ^ n)) *
      (Fintype.card (FrequencyTree (S × S) n) : ℝ) by positivity)).trans
      ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpriorcost
        (Nat.cast_nonneg _)) (by positivity)).trans (herrors S hcard))
  apply hsum.trans
  nlinarith only [hcost, he]

end Ostmann

end OAI
