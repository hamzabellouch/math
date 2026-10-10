import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

namespace OAI

/-!
# Exact resource exponents

Rational arithmetic for `res:tuple-exponent` and `res:exponent-relations` in
*A Low-Space Algorithm for Worst-Case Subset Sum*. The numerical hypotheses
relate leaf, dictionary, buffer, and raw-tuple exponential rates.
-/

namespace LowSpaceSubsetSum

open Filter Asymptotics

/-- The block size is divisible by eight; `n` counts indices, not input bits. -/
def mixerSize (n : ℕ) : ℕ := 8 * (3 * n / 100)

theorem mixerSize_bounds (n : ℕ) :
    (6 / 25 : ℝ) * n - 8 < mixerSize n ∧
      (mixerSize n : ℝ) ≤ (6 / 25 : ℝ) * n := by
  have hmod := Nat.mod_lt (3 * n) (by norm_num : 0 < 100)
  have heq := Nat.mod_add_div (3 * n) 100
  have hlow : 3 * n < 100 * (3 * n / 100 + 1) := by omega
  have hupp : 100 * (3 * n / 100) ≤ 3 * n := by omega
  have hl : (3 : ℝ) * n < 100 * ((3 * n / 100 : ℕ) + 1 : ℝ) := by
    exact_mod_cast hlow
  have hu : (100 : ℝ) * (3 * n / 100 : ℕ) ≤ 3 * n := by
    exact_mod_cast hupp
  simp only [mixerSize, Nat.cast_mul, Nat.cast_ofNat]
  constructor <;> linarith

/-- Analysis scale for the number of low-filtered raw child pairs. -/
noncomputable def pairExponent (n m h fmax : ℝ) : ℝ :=
  n / 4 + (-5 / 4 + 3 / 2 * h) * m + fmax

/-- Analysis scale for distinct valid parent entries. -/
noncomputable def entryExponent (n m hbar d f0 : ℝ) : ℝ :=
  n / 2 + (hbar - 1) * m - d + f0

/-- The additional-prime exponent. -/
noncomputable def extraPrimeExponent (n m fmax : ℝ) : ℝ :=
  n / 4 + (4 / 125) * m - fmax

/-- Regenerating the pair streams preserves the exact half-exponential rate. -/
theorem regeneration_exponent (n m h fmax : ℝ)
    (hm : 0 ≤ m) (hh : h ≤ 4057 / 5000) :
    extraPrimeExponent n m fmax + pairExponent n m h fmax ≤ n / 2 := by
  dsimp [extraPrimeExponent, pairExponent]
  nlinarith [mul_nonneg (sub_nonneg.mpr hh) hm]

/-- The separator occurrence factor also preserves the exact time rate. -/
theorem matching_exponent (n m h hbar d f0 : ℝ)
    (hm : 0 ≤ m) (hh : hbar ≤ h) (hf : f0 ≤ d) :
    entryExponent n m hbar d f0 + (1 - h) * m ≤ n / 2 := by
  dsimp [entryExponent]
  nlinarith [mul_nonneg (sub_nonneg.mpr hh) hm]

/-- The extra prime has a strict margin over the space-scaled entry count. -/
theorem bucket_exponent_gap (n m h hbar d f0 fmax : ℝ)
    (hn : 10000 ≤ n) (hm : (6 / 25) * n - 8 ≤ m)
    (hh : h ≤ 4057 / 5000) (hbar_le : hbar ≤ h)
    (hf0 : f0 ≤ d / 2) (hfmax : fmax ≤ d / 2 + n / 4000) :
    (3 / 2000) * n ≤
      extraPrimeExponent n m fmax - (entryExponent n m hbar d f0 - (199 / 1000) * n) := by
  have hm0 : 0 ≤ m := by linarith
  have hprod := mul_nonneg (sub_nonneg.mpr (hbar_le.trans hh)) hm0
  dsimp [extraPrimeExponent, entryExponent]
  nlinarith

/-- Raw four-leaf tuple counts fit the exact time exponent after low filtering. -/
theorem tuple_exponent (n m h beta f0 fj : ℝ)
    (hn : 3000 ≤ n) (hm : (6 / 25) * n - 8 ≤ m)
    (hh : h ≤ 4057 / 5000)
    (hb : beta ≤ n / 4 + (-3 / 4 + 3 / 2 * h) * m)
    (hf0 : f0 ≤ (39 / 5000) * n) (hfj : fj ≤ (39 / 5000) * n) :
    2 * beta - (m / 2 - f0) - (m / 2 - fj) ≤ n / 2 := by
  have hm0 : 0 ≤ m := by linarith
  have hprod := mul_nonneg (sub_nonneg.mpr hh) hm0
  nlinarith

/-- Every raw leaf is below the buffer and dictionary rates with fixed slack. -/
theorem leaf_exponent (n m h beta : ℝ)
    (hm0 : 0 ≤ m) (hm : m ≤ (6 / 25) * n)
    (hh : h ≤ 4057 / 5000)
    (hb : beta ≤ n / 4 + (-3 / 4 + 3 / 2 * h) * m) :
    beta / 2 ≤ (45263 / 250000) * n := by
  have hprod := mul_nonneg (sub_nonneg.mpr hh) hm0
  nlinarith

/-- A fixed polynomial is eventually absorbed by any positive base-two rate. -/
theorem polynomial_absorption (k : ℕ) {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ k ≤ (2 : ℝ) ^ (eps * n) := by
  have hb : 0 < Real.log 2 * eps := mul_pos (Real.log_pos (by norm_num)) heps
  have h := (isLittleO_pow_exp_pos_mul_atTop k hb).comp_tendsto
    (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [h.eventuallyLE] with n hn
  have hk : 0 ≤ (n : ℝ) ^ k := pow_nonneg (Nat.cast_nonneg _) _
  simpa only [Function.comp_apply, Real.norm_eq_abs, abs_of_nonneg hk,
    abs_of_pos (Real.exp_pos _),
    Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), mul_assoc] using hn

/-- The polynomial-bit promise gives a polynomial bound with no input for `c`. -/
theorem polynomial_bit_bound {n b c : ℕ} (hn : 2 ≤ n) (hc : 0 < c)
    (hb : b ≤ n ^ c) : n + b + 2 ≤ 3 * n ^ c := by
  have hpow : n ≤ n ^ c := le_self_pow (by omega) (by omega)
  omega

/-- The ordinary exponential space corollary, as a numeric bound implication.

This applies to an actual algorithm only after its intermediate space bound
has been established; it is not a replacement for that main theorem.
-/
theorem absorb_space_polynomial {rho : ℝ} (hrho : (199 / 1000 : ℝ) < rho)
    (c : ℕ) (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, ∀ b : ℕ, b ≤ n ^ c →
      ((n + b + 2 : ℕ) : ℝ) ^ 15 * (2 : ℝ) ^ ((199 / 1000 : ℝ) * n) ≤
        (3 : ℝ) ^ 15 * (2 : ℝ) ^ (rho * n) := by
  filter_upwards [polynomial_absorption (15 * c) (sub_pos.mpr hrho),
    eventually_ge_atTop 2] with n hn hn2
  intro b hb
  have hu : ((n + b + 2 : ℕ) : ℝ) ≤ 3 * (n : ℝ) ^ c := by
    exact_mod_cast polynomial_bit_bound hn2 hc hb
  have hu15 := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (n + b + 2 : ℕ)) hu 15
  have hp : (3 * (n : ℝ) ^ c) ^ 15 = (3 : ℝ) ^ 15 * (n : ℝ) ^ (15 * c) := by
    rw [mul_pow, ← pow_mul, Nat.mul_comm c 15]
  rw [hp] at hu15
  calc
    ((n + b + 2 : ℕ) : ℝ) ^ 15 * (2 : ℝ) ^ ((199 / 1000 : ℝ) * n)
        ≤ ((3 : ℝ) ^ 15 * (n : ℝ) ^ (15 * c)) *
          (2 : ℝ) ^ ((199 / 1000 : ℝ) * n) :=
      mul_le_mul_of_nonneg_right hu15 (Real.rpow_nonneg (by norm_num) _)
    _ ≤ ((3 : ℝ) ^ 15 * (2 : ℝ) ^ ((rho - 199 / 1000) * n)) *
          (2 : ℝ) ^ ((199 / 1000 : ℝ) * n) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hn (by positivity))
        (Real.rpow_nonneg (by norm_num) _)
    _ = (3 : ℝ) ^ 15 * (2 : ℝ) ^ (rho * n) := by
      rw [mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 2
      ring

/-- The chosen exponent `1/5` has the strict margin needed for absorption. -/
theorem one_fifth_space_polynomial (c : ℕ) (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, ∀ b : ℕ, b ≤ n ^ c →
      ((n + b + 2 : ℕ) : ℝ) ^ 15 * (2 : ℝ) ^ ((199 / 1000 : ℝ) * n) ≤
        (3 : ℝ) ^ 15 * (2 : ℝ) ^ ((1 / 5 : ℝ) * n) :=
  absorb_space_polynomial (rho := (1 / 5 : ℝ)) (by norm_num) c hc

end LowSpaceSubsetSum

end OAI
