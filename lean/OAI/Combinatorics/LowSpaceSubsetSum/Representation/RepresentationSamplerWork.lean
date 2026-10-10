import OAI.Combinatorics.LowSpaceSubsetSum.Counting.SamplerAttempts
import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationHistoryCoupling

namespace OAI

/-! # Candidate and divisor counts for the representation sampler

The counts include all `n³` attempts on exhaustion. Family occurrences are
counted separately even when their sampled subsets coincide. These are
candidate-read and remainder-test counts, before the word-operation ledger.
-/

noncomputable section

namespace LowSpaceSubsetSum

open scoped BigOperators

namespace SeparatorExpectation.RoundedParameters

variable {g : ℕ} (S : RoundedParameters g)

/-- The actual number of permutation range calls for all four families. -/
def rangeCalls : ℕ := ∑ i : Fin 4, S.counts i * g

theorem rangeCalls_le : S.rangeCalls ≤ 44 * g * 2 ^ g := by
  calc
    _ ≤ ∑ _i : Fin 4, 11 * 2 ^ g * g := by
      exact Finset.sum_le_sum (fun i _ => Nat.mul_le_mul_right g (S.counts_le i))
    _ = _ := by simp; ring

end SeparatorExpectation.RoundedParameters

namespace RepresentationSetup

variable {n : ℕ} (R : RepresentationSetup n)

/-- The low factors and the extra prime, in their sampling order. Factors
whose width is below four use the constant one and incur no prime test. -/
def samplerPrimeWidths (z : Layout n) : Fin 4 → ℕ :=
  ![R.factorExponents z 0, R.factorExponents z 1,
    R.factorExponents z 2, R.extraPrimeParameter z]

theorem factorExponents_le_half (z : Layout n) (i : Fin 3) :
    R.factorExponents z i ≤ R.halfSize := by
  have hf (j : Fin 3) : ⌊R.lowExponent z j⌋₊ ≤ R.halfSize :=
    Nat.floor_le_of_le (R.lowExponent_le_halfSize z j)
  have h0 := hf 0
  have h1 := hf 1
  have h2 := hf 2
  fin_cases i
  · exact h2
  · change ⌊R.lowExponent z 1⌋₊ - ⌊R.lowExponent z 2⌋₊ ≤ R.halfSize
    omega
  · change ⌊R.lowExponent z 0⌋₊ - ⌊R.lowExponent z 1⌋₊ ≤ R.halfSize
    omega

theorem halfSize_rate : (R.halfSize : ℝ) ≤ (3 / 25 : ℝ) * n := by
  have hm := (mixerSize_bounds n).2
  have hh : (R.halfSize : ℝ) ≤ (mixerSize n : ℝ) / 2 := by
    have he : (R.halfSize : ℝ) * 2 ≤ (mixerSize n : ℝ) := by
      exact_mod_cast Nat.div_mul_le_self (mixerSize n) 2
    linarith
  linarith

/-- The `0.258 n` bound includes both floor losses. -/
theorem samplerPrimeWidths_rate (z : Layout n) (hn : 100 ≤ n) (i : Fin 4) :
    (R.samplerPrimeWidths z i : ℝ) ≤ (129 / 500 : ℝ) * n := by
  have hf (j : Fin 3) : (R.factorExponents z j : ℝ) ≤ (3 / 25 : ℝ) * n := by
    have hc : (R.factorExponents z j : ℝ) ≤ R.halfSize := by
      exact_mod_cast R.factorExponents_le_half z j
    exact hc.trans R.halfSize_rate
  have he := (R.extraPrimeParameter_bounds z hn).2.trans (R.extraPrimeRate_bounds z).2
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  fin_cases i
  · exact (hf 0).trans (by linarith)
  · exact (hf 1).trans (by linarith)
  · exact (hf 2).trans (by linarith)
  · exact he.trans (by linarith)

theorem sampler_divisor_exponent (z : Layout n) (hn : 100 ≤ n) (i : Fin 4) :
    (((R.samplerPrimeWidths z i + 1) / 2 : ℕ) : ℝ) ≤
      (129 / 1000 : ℝ) * n + 1 / 2 := by
  have h := R.samplerPrimeWidths_rate z hn i
  have hd := Nat.div_mul_le_self (R.samplerPrimeWidths z i + 1) 2
  have hdR : (((R.samplerPrimeWidths z i + 1) / 2 : ℕ) : ℝ) * 2 ≤
      (R.samplerPrimeWidths z i : ℝ) + 1 := by exact_mod_cast hd
  linarith

theorem sampler_divisor_bound (z : Layout n) (hn : 100 ≤ n) (i : Fin 4) :
    ((2 ^ ((R.samplerPrimeWidths z i + 1) / 2) : ℕ) : ℝ) ≤
      (2 : ℝ) ^ ((n : ℝ) / 2) := by
  rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have h := R.sampler_divisor_exponent z hn i
  have hnR : (100 : ℝ) ≤ n := by exact_mod_cast hn
  linarith

theorem separator_width_rate : (2 * blockHalf n 0 : ℕ) ≤ n / 2 := by
  simp only [blockHalf, Matrix.cons_val_zero]
  omega

/-- The calls outside the families are the whole-input permutation, three
block permutations, three size guesses, and three low-residue draws. -/
def actualRangeCalls (h : R.PrimeHistory) (hn : 2200 ≤ n) : ℕ :=
  n + 3 * mixerSize n + 6 + (separatorParameters h.1.1.2 hn).rangeCalls

theorem actualRangeCalls_le (h : R.PrimeHistory) (hn : 2200 ≤ n) :
    R.actualRangeCalls h hn ≤ R.rangeCallBound := by
  unfold actualRangeCalls rangeCallBound
  exact Nat.add_le_add_left (SeparatorExpectation.RoundedParameters.rangeCalls_le _) _

theorem rangeCallBound_half : (R.rangeCallBound : ℝ) ≤
    56 * (n + 1 : ℝ) * (2 : ℝ) ^ ((n : ℝ) / 2) := by
  have hm : mixerSize n ≤ n := by
    have h := Finset.card_le_univ (R.mixers 0)
    simpa only [R.card, Fintype.card_fin] using h
  have hg := separator_width_rate (n := n)
  have hg' : 2 * blockHalf n 0 ≤ n := hg.trans (Nat.div_le_self _ _)
  have hp : (1 : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) / 2) :=
    Real.one_le_rpow (by norm_num) (by positivity)
  have hpow : ((2 ^ (2 * blockHalf n 0) : ℕ) : ℝ) ≤
      (2 : ℝ) ^ ((n : ℝ) / 2) := by
    rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have hgR : (2 * blockHalf n 0 : ℕ) * 2 ≤ n := by omega
    have hgR' : ((2 * blockHalf n 0 : ℕ) : ℝ) * 2 ≤ n := by exact_mod_cast hgR
    linarith
  have hmR : (mixerSize n : ℝ) ≤ n := by exact_mod_cast hm
  have hgR : ((2 * blockHalf n 0 : ℕ) : ℝ) ≤ n := by exact_mod_cast hg'
  have hlarge := mul_le_mul_of_nonneg_left hpow
    (show (0 : ℝ) ≤ 44 * (2 * blockHalf n 0 : ℕ) by positivity)
  have hsmall := mul_le_mul_of_nonneg_left hp
    (show (0 : ℝ) ≤ n + 3 * (mixerSize n : ℝ) + 6 by positivity)
  push_cast at hlarge hgR
  unfold rangeCallBound
  push_cast
  nlinarith [mul_nonneg (sub_nonneg.mpr hgR)
    (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) ((n : ℝ) / 2))]

/-- Upper tally of the random candidates read, including all four possible
prime calls and one direct Boolean draw for each sign coordinate. -/
def samplerCandidateBudget : ℕ := n + n ^ 3 * (R.rangeCallBound + 4)

/-- Each term is the all-attempts bound for the counted `primeRun`. -/
def samplerDivisorBudget (z : Layout n) : ℕ :=
  ∑ i : Fin 4, n ^ 3 * 2 ^ ((R.samplerPrimeWidths z i + 1) / 2)

theorem samplerDivisorBudget_half (z : Layout n) (hn : 100 ≤ n) :
    (R.samplerDivisorBudget z : ℝ) ≤
      4 * (n : ℝ) ^ 3 * (2 : ℝ) ^ ((n : ℝ) / 2) := by
  unfold samplerDivisorBudget
  rw [Nat.cast_sum]
  calc
    _ ≤ ∑ _i : Fin 4, (n : ℝ) ^ 3 * (2 : ℝ) ^ ((n : ℝ) / 2) := by
      apply Finset.sum_le_sum
      intro i _
      push_cast
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast R.sampler_divisor_bound z hn i)
        (by positivity)
    _ = _ := by simp; ring

theorem sampler_operations_half (z : Layout n) (hn : 100 ≤ n) :
    (R.samplerCandidateBudget + R.samplerDivisorBudget z : ℕ) ≤
      100 * (inputScale R.input : ℝ) ^ 4 * (2 : ℝ) ^ ((n : ℝ) / 2) := by
  have hc := R.rangeCallBound_half
  have hd := R.samplerDivisorBudget_half z hn
  have hp : (1 : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) / 2) :=
    Real.one_le_rpow (by norm_num) (by positivity)
  have hnu : (n + 1 : ℝ) ≤ inputScale R.input := by
    exact_mod_cast (show n + 1 ≤ inputScale R.input by unfold inputScale; omega)
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hn3 : (n : ℝ) ^ 3 ≤ (n + 1 : ℝ) ^ 3 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 3
  have hu4 := pow_le_pow_left₀ (by positivity) hnu 4
  have hC := mul_le_mul_of_nonneg_left hc (show (0 : ℝ) ≤ (n : ℝ) ^ 3 by positivity)
  have hC' := mul_le_mul_of_nonneg_right hu4
    (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) ((n : ℝ) / 2))
  have hnE := mul_le_mul_of_nonneg_left hp hn0
  have hn3E := mul_le_mul_of_nonneg_left hp (show (0 : ℝ) ≤ (n : ℝ) ^ 3 by positivity)
  unfold samplerCandidateBudget
  push_cast
  nlinarith [mul_nonneg (sub_nonneg.mpr hn3)
    (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) ((n : ℝ) / 2))]

end RepresentationSetup
end LowSpaceSubsetSum

end

end OAI
