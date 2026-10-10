import OAI.NumberTheory.TwoPoint.Bounds.FiniteResidueComparison
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace OAI

/-! Explicit large-scale choices for the finite residue comparison. -/

namespace TwoPointCorrelations

open Filter Finset

/-- Fixed coefficients are absorbed by increasing a positive integer power. -/
lemma eventually_const_mul_pow_le (p q : ℕ) (hpq : p < q) (c : ℝ) :
    ∀ᶠ L : ℝ in atTop, c * L ^ p ≤ L ^ q := by
  filter_upwards [eventually_ge_atTop 1, eventually_ge_atTop c] with L hL hc
  calc
    c * L ^ p ≤ L * L ^ p := mul_le_mul_of_nonneg_right hc (pow_nonneg (by linarith) _)
    _ = L ^ (p + 1) := by rw [pow_succ]; ring
    _ ≤ L ^ q := pow_le_pow_right₀ hL hpq

lemma ceil_pow_bounds {L : ℝ} (hL : 1 ≤ L) (k : ℕ) :
    L ^ k ≤ (⌈L ^ k⌉₊ : ℝ) ∧ (⌈L ^ k⌉₊ : ℝ) ≤ 2 * L ^ k := by
  have hp : 1 ≤ L ^ k := one_le_pow₀ hL
  exact ⟨Nat.le_ceil _, (Nat.ceil_lt_add_one (by positivity : 0 ≤ L ^ k)).le.trans (by linarith)⟩

/-- Truth-table substitution fits the manuscript's encoded size bound. -/
lemma eventually_encoded_size_bound :
    ∀ᶠ L : ℝ in atTop, ∀ B : ℕ, B = ⌈L ^ 15⌉₊ →
      ∀ S : ℝ, S ≤ Real.exp (L ^ 6) →
      (1 + (2 : ℝ) ^ B * (1 + B)) * S ≤ Real.exp (L ^ 17) := by
  filter_upwards [eventually_ge_atTop 1,
    eventually_const_mul_pow_le 15 17 (by norm_num) 7] with L hL hpow B hB S hS
  have hLp : 0 ≤ L := le_trans zero_le_one hL
  have hBbound : (B : ℝ) ≤ 2 * L ^ 15 := by simpa only [hB] using (ceil_pow_bounds hL 15).2
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hpowB : (2 : ℝ) ^ B ≤ Real.exp (B : ℝ) := by
    calc
      _ ≤ (Real.exp 1) ^ B := pow_le_pow_left₀ (by norm_num) htwo B
      _ = Real.exp (B : ℝ) := by rw [← Real.exp_nat_mul]; simp
  have honeB : 1 + (B : ℝ) ≤ Real.exp (B : ℝ) := by
    simpa [add_comm] using Real.add_one_le_exp (B : ℝ)
  have hfac : 1 + (2 : ℝ) ^ B * (1 + B) ≤ Real.exp (1 + 2 * (B : ℝ)) := by
    calc
      _ ≤ 1 + Real.exp (B : ℝ) * Real.exp (B : ℝ) :=
        add_le_add (le_refl 1) (mul_le_mul hpowB honeB (by positivity) (by positivity))
      _ = 1 + Real.exp (2 * (B : ℝ)) := by rw [← Real.exp_add]; congr 2; ring
      _ ≤ 2 * Real.exp (2 * (B : ℝ)) := by
        have := Real.one_le_exp_iff.mpr (show 0 ≤ 2 * (B : ℝ) by positivity)
        linarith
      _ ≤ Real.exp 1 * Real.exp (2 * (B : ℝ)) :=
        mul_le_mul_of_nonneg_right htwo (Real.exp_pos _).le
      _ = _ := (Real.exp_add _ _).symm
  have hsmall : L ^ 6 ≤ L ^ 15 := pow_le_pow_right₀ hL (by norm_num)
  calc
    _ ≤ (1 + (2 : ℝ) ^ B * (1 + B)) * Real.exp (L ^ 6) :=
      mul_le_mul_of_nonneg_left hS (by positivity)
    _ ≤ Real.exp (1 + 2 * (B : ℝ)) * Real.exp (L ^ 6) :=
      mul_le_mul_of_nonneg_right hfac (Real.exp_pos _).le
    _ = Real.exp (1 + 2 * (B : ℝ) + L ^ 6) := (Real.exp_add _ _).symm
    _ ≤ Real.exp (7 * L ^ 15) := by
      apply Real.exp_le_exp.mpr
      have hp : 1 ≤ L ^ 15 := one_le_pow₀ hL
      nlinarith
    _ ≤ _ := Real.exp_le_exp.mpr hpow

/-- The number of bits is small even after adding the fixed-modulus block. -/
lemma eventually_bit_count_bound :
    ∀ᶠ L : ℝ in atTop, ∀ m B : ℕ, (m : ℝ) ≤ Real.exp L + 1 → B = ⌈L ^ 15⌉₊ →
      ((m * B : ℕ) : ℝ) ≤ Real.exp (2 * L) := by
  have h := (Real.isLittleO_pow_exp_atTop (n := 15)).bound (show 0 < (1 / 4 : ℝ) by norm_num)
  filter_upwards [eventually_ge_atTop 1, h] with L hL hpow m B hm hB
  have hLp : 0 ≤ L := le_trans zero_le_one hL
  have hp : 0 ≤ L ^ 15 := pow_nonneg hLp _
  have h4 : 4 * L ^ 15 ≤ Real.exp L := by
    rw [Real.norm_eq_abs, abs_of_nonneg hp, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at hpow
    linarith
  have hm' : (m : ℝ) ≤ 2 * Real.exp L := by
    have := Real.one_le_exp_iff.mpr hLp
    linarith
  have hB' : (B : ℝ) ≤ 2 * L ^ 15 := by simpa only [hB] using (ceil_pow_bounds hL 15).2
  calc
    ((m * B : ℕ) : ℝ) = (m : ℝ) * (B : ℝ) := by push_cast; rfl
    _ ≤ (2 * Real.exp L) * (2 * L ^ 15) := mul_le_mul hm' hB' (by positivity) (by positivity)
    _ = Real.exp L * (4 * L ^ 15) := by ring
    _ ≤ Real.exp L * Real.exp L := mul_le_mul_of_nonneg_left h4 (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

/-- Polynomially many independence coordinates suffice for Braverman's
logarithmic requirement at encoded size `exp (L^17)`. -/
lemma eventually_braverman_budget (K C : ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ S : ℝ, 1 ≤ S → S ≤ Real.exp (L ^ 17) →
      (K : ℝ) * (Real.log (S / Real.exp (-(L ^ 11)))) ^ C ≤
        (⌈L ^ (17 * C + 1)⌉₊ : ℝ) := by
  filter_upwards [eventually_ge_atTop 1,
    eventually_const_mul_pow_le (17 * C) (17 * C + 1) (by omega) ((K : ℝ) * 2 ^ C)]
    with L hL hpow S hS hlo
  have hSpos : 0 < S := lt_of_lt_of_le zero_lt_one hS
  have hlog : Real.log (S / Real.exp (-(L ^ 11))) ≤ 2 * L ^ 17 := by
    rw [Real.log_div hSpos.ne' (Real.exp_pos _).ne', Real.log_exp]
    have hl := Real.log_le_log hSpos hlo
    rw [Real.log_exp] at hl
    have hsmall : L ^ 11 ≤ L ^ 17 := pow_le_pow_right₀ hL (by norm_num)
    linarith
  have hlogpos : 0 ≤ Real.log (S / Real.exp (-(L ^ 11))) := by
    apply Real.log_nonneg
    apply (le_div_iff₀ (Real.exp_pos _)).mpr
    have he : Real.exp (-(L ^ 11)) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (pow_nonneg (le_trans zero_le_one hL) _))
    simpa using he.trans hS
  calc
    _ ≤ (K : ℝ) * (2 * L ^ 17) ^ C :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlogpos hlog C) (Nat.cast_nonneg _)
    _ = ((K : ℝ) * 2 ^ C) * L ^ (17 * C) := by rw [mul_pow, ← pow_mul]; ring
    _ ≤ L ^ (17 * C + 1) := hpow
    _ ≤ _ := Nat.le_ceil _

/-- The actual low-order Fourier mass is exponentially small once the
interval exponent exceeds the independence exponent. -/
lemma eventually_fourier_budget (T A : ℕ) (hT : 10 ≤ T) (hA : T + 1 < A) :
    ∀ᶠ L : ℝ in atTop, ∀ t n N : ℕ, t = ⌈L ^ T⌉₊ →
      (n : ℝ) ≤ Real.exp (2 * L) → Real.exp (L ^ A / 2) ≤ (N : ℝ) →
      ((Real.exp L) ^ t / (N : ℝ)) * ((t + 1 : ℕ) : ℝ) * (n : ℝ) ^ t ≤
        Real.exp (-(L ^ 11)) := by
  filter_upwards [eventually_ge_atTop 1,
    eventually_const_mul_pow_le (T + 1) A hA 20] with L hL hpower t n N ht hn hN
  have hLp : 0 ≤ L := le_trans zero_le_one hL
  have htbound : (t : ℝ) ≤ 2 * L ^ T := by simpa only [ht] using (ceil_pow_bounds hL T).2
  have htp : 1 ≤ L ^ T := one_le_pow₀ hL
  have htadd : (t : ℝ) + 1 ≤ 3 * L ^ T := by linarith
  have hNt : 0 < (N : ℝ) := lt_of_lt_of_le (Real.exp_pos _) hN
  have htExp : ((t + 1 : ℕ) : ℝ) ≤ Real.exp ((t : ℝ) + 1) := by
    push_cast
    have h := Real.add_one_le_exp ((t : ℝ) + 1)
    linarith
  have hcalc : (((Real.exp L) ^ t / Real.exp (L ^ A / 2)) *
      Real.exp ((t : ℝ) + 1)) * (Real.exp (2 * L)) ^ t =
      Real.exp (3 * L * (t : ℝ) + ((t : ℝ) + 1) - L ^ A / 2) := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_sub,
      ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hsmall : L ^ T ≤ L ^ (T + 1) := pow_le_pow_right₀ hL (by omega)
  have h11 : L ^ 11 ≤ L ^ (T + 1) := pow_le_pow_right₀ hL (by omega)
  have hterm : L * (t : ℝ) ≤ 2 * L ^ (T + 1) := by
    have h := mul_le_mul_of_nonneg_left htbound hLp
    rw [pow_succ]
    nlinarith
  calc
    _ ≤ (((Real.exp L) ^ t / Real.exp (L ^ A / 2)) *
        Real.exp ((t : ℝ) + 1)) * (Real.exp (2 * L)) ^ t := by
      gcongr
    _ = _ := hcalc
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      linarith

/-- Both decoder errors and the corrected-law errors fit inside the final
`exp (-L^10)` budget. -/
lemma eventually_total_comparison_error :
    ∀ᶠ L : ℝ in atTop, ∀ B : ℕ, B = ⌈L ^ 15⌉₊ → ∀ D : ℝ,
      D ≤ Real.exp (3 * L) →
      2 * D / (2 : ℝ) ^ B + 3 * Real.exp (-(L ^ 11)) / 2 +
        Real.exp (-(L ^ 11)) ≤ Real.exp (-(L ^ 10)) := by
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  filter_upwards [eventually_ge_atTop 4,
    eventually_const_mul_pow_le 11 15 (by norm_num) (6 / Real.log (2 : ℝ))]
    with L hL4 hpower B hB D hD
  have hL : 1 ≤ L := by linarith
  have hLp : 0 ≤ L := le_trans zero_le_one hL
  have hBbound : L ^ 15 ≤ (B : ℝ) := by simpa only [hB] using (ceil_pow_bounds hL 15).1
  have hdom : 6 * L ^ 11 ≤ L ^ 15 * Real.log (2 : ℝ) := by
    apply (div_le_iff₀ hlog).mp
    convert hpower using 1; ring
  have hlogmax : Real.log (2 : ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show 0 < (2 : ℝ) by norm_num)
    linarith
  have h11one : 1 ≤ L ^ 11 := one_le_pow₀ hL
  have hL11 : L ≤ L ^ 11 := by simpa using pow_le_pow_right₀ hL (show 1 ≤ (11 : ℕ) by norm_num)
  have hmul : L ^ 15 * Real.log (2 : ℝ) ≤ (B : ℝ) * Real.log (2 : ℝ) :=
    mul_le_mul_of_nonneg_right hBbound hlog.le
  have hdecodeExp : Real.log (2 : ℝ) + 3 * L - (B : ℝ) * Real.log (2 : ℝ) ≤ -(L ^ 11) := by
    linarith
  have hpowB : (2 : ℝ) ^ B = Real.exp ((B : ℝ) * Real.log (2 : ℝ)) := by
    rw [Real.exp_nat_mul, Real.exp_log (show 0 < (2 : ℝ) by norm_num)]
  have hdecode : 2 * D / (2 : ℝ) ^ B ≤ Real.exp (-(L ^ 11)) := by
    calc
      _ ≤ 2 * Real.exp (3 * L) / (2 : ℝ) ^ B := by gcongr
      _ = Real.exp (Real.log (2 : ℝ) + 3 * L - (B : ℝ) * Real.log (2 : ℝ)) := by
        rw [hpowB, Real.exp_sub, Real.exp_add,
          Real.exp_log (show 0 < (2 : ℝ) by norm_num)]
      _ ≤ _ := Real.exp_le_exp.mpr hdecodeExp
  have h10one : 1 ≤ L ^ 10 := one_le_pow₀ hL
  have h11grow : 4 * L ^ 10 ≤ L ^ 11 := by
    calc
      4 * L ^ 10 ≤ L * L ^ 10 := mul_le_mul_of_nonneg_right hL4 (pow_nonneg hLp 10)
      _ = L ^ 11 := by ring
  have hfour : (4 : ℝ) ≤ Real.exp 3 := by
    linarith [Real.add_one_le_exp (3 : ℝ)]
  calc
    _ ≤ 4 * Real.exp (-(L ^ 11)) := by linarith [Real.exp_pos (-(L ^ 11))]
    _ ≤ Real.exp 3 * Real.exp (-(L ^ 11)) :=
      mul_le_mul_of_nonneg_right hfour (Real.exp_pos _).le
    _ = Real.exp (3 - L ^ 11) := by rw [← Real.exp_add]; rfl
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

/-- The coefficient mass allowed in scalar expansions consumes only one
power in the exponent of the finite-law error. -/
lemma eventually_scalar_error (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ L : ℝ in atTop,
      Real.exp (C * L ^ 5) * Real.exp (-(L ^ 10)) ≤ Real.exp (-(L ^ 9)) := by
  filter_upwards [eventually_ge_atTop 1,
    eventually_const_mul_pow_le 9 10 (by norm_num) (C + 1)] with L hL hpower
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hsmall : L ^ 5 ≤ L ^ 9 := pow_le_pow_right₀ hL (by norm_num)
  have hmul := mul_le_mul_of_nonneg_left hsmall hC
  nlinarith

end TwoPointCorrelations

end OAI
