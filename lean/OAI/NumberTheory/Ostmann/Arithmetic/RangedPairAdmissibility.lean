import OAI.NumberTheory.Ostmann.Arithmetic.RangedPairNumericBudget

namespace OAI

/-! # The actual periods and frequencies fit below the separated prime scales -/

namespace Ostmann
open Filter

/-- A fixed-depth polynomial period is below the long-prime cutoff. Every
actual frequency is also below the smallest retained prime. -/
theorem eventual_word_pair_admissible (n : ℕ) (b C z α β c : ℝ)
    (hb : 0 ≤ b) (hC : 0 ≤ C) (hz : 0 ≤ z) (hα : 0 < α)
    (hαβ : α < β) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop, ∀ (t t' : FrequencyTree ℤ n)
      (B V A : ℕ) (lower m : ℝ),
      0 ≤ m → m ≤ z * L → (B : ℝ) ≤ b * (1 + m) →
      (V : ℝ) ≤ Real.exp (C * (1 + m)) →
      (∀ s ∈ allFrequencyList n t, s.natAbs ≤ V) →
      (∀ s ∈ allFrequencyList n t', s.natAbs ≤ V) →
      Real.exp (c * Real.exp (α * L)) ≤ lower →
      Real.exp (Real.exp (β * L)) ≤ (A : ℝ) →
      wordTransferFullPeriod n t B * wordTransferFullPeriod n t' B ≤ A ∧
      (∀ p : ℕ, lower ≤ (p : ℝ) → ∀ s ∈ allFrequencyList n t, s.natAbs < p) ∧
      (∀ p : ℕ, lower ≤ (p : ℝ) → ∀ s ∈ allFrequencyList n t', s.natAbs < p) := by
  let K := 2 * C * wordPeriodExponent n b
  have hK : 0 ≤ K := by dsimp [K, wordPeriodExponent]; positivity
  have hβ : 0 < β := hα.trans hαβ
  filter_upwards [eventual_polynomial_log_budget K z β 1 (n + 2) hK hz hβ (by norm_num),
    eventual_polynomial_log_budget C z α (c / 2) 1 hC hz hα (by positivity)]
    with L hperiod hfreq
  intro t t' B V A lower m hm hmL hB hV hf hf' hlower hA
  have hp := wordTransferFullPeriod_le_exp n t B V b C m hC hm hB hV hf
  have hp' := wordTransferFullPeriod_le_exp n t' B V b C m hC hm hB hV hf'
  have hMA : wordTransferFullPeriod n t B * wordTransferFullPeriod n t' B ≤ A := by
    have hexp := hperiod m hm hmL
    simp only [one_mul] at hexp
    have hmulp : ((wordTransferFullPeriod n t B * wordTransferFullPeriod n t' B : ℕ) : ℝ) ≤
        Real.exp (K * (1 + m) ^ (n + 2)) := by
      push_cast
      apply (mul_le_mul hp hp' (by positivity) (Real.exp_nonneg _)).trans_eq
      rw [← Real.exp_add]
      congr 1
      dsimp [K]
      ring
    exact_mod_cast hmulp.trans ((Real.exp_le_exp.mpr hexp).trans hA)
  have hVlow : (V : ℝ) < lower := by
    have hfl := hfreq m hm hmL
    simp only [pow_one] at hfl
    have hstrict : C * (1 + m) < c * Real.exp (α * L) := by
      nlinarith only [hfl, mul_pos hc (Real.exp_pos (α * L))]
    exact hV.trans_lt ((Real.exp_lt_exp.mpr hstrict).trans_le hlower)
  refine ⟨hMA, ?_, ?_⟩
  · intro p hp s hs
    have hsp : (s.natAbs : ℝ) < (p : ℝ) :=
      (Nat.cast_le.mpr (hf s hs)).trans_lt (hVlow.trans_le hp)
    exact_mod_cast hsp
  · intro p hp s hs
    have hsp : (s.natAbs : ℝ) < (p : ℝ) :=
      (Nat.cast_le.mpr (hf' s hs)).trans_lt (hVlow.trans_le hp)
    exact_mod_cast hsp

end Ostmann

end OAI
