import OAI.NumberTheory.TwoPoint.Bounds.DilatedWindowScale

namespace OAI

/-! Uniform parameter bounds for the exact smooth-divisor MRT reduction. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

lemma dilation_quotient_log_upper (B C₀ : ℝ) (D a : ℕ)
    (hB : 1 ≤ B) (hDpos : 0 < D)
    (hD : (D : ℝ) ≤ Real.exp (C₀ * B ^ (2 : ℕ))) :
    Real.log (D / a + 1 : ℕ) ≤ (C₀ + 1) * B ^ (2 : ℕ) := by
  have hM : (0 : ℝ) < (D / a + 1 : ℕ) := by positivity
  have hMbound : (D / a + 1 : ℕ) ≤ 2 * (D : ℝ) := by
    have hd : D / a + 1 ≤ 2 * D := by have hh := Nat.div_le_self D a; omega
    exact_mod_cast hd
  have hBsq : 1 ≤ B ^ (2 : ℕ) := one_le_pow₀ hB
  have hexp : 2 ≤ Real.exp (B ^ (2 : ℕ)) := by
    have hh := Real.add_one_le_exp (B ^ (2 : ℕ)); linarith
  have hlast : (2 : ℝ) * Real.exp (C₀ * B ^ (2 : ℕ)) ≤
      Real.exp ((C₀ + 1) * B ^ (2 : ℕ)) := by
    calc
      _ ≤ Real.exp (B ^ (2 : ℕ)) * Real.exp (C₀ * B ^ (2 : ℕ)) :=
        mul_le_mul_of_nonneg_right hexp (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  exact (Real.log_le_log hM
    (hMbound.trans ((mul_le_mul_of_nonneg_left hD (by norm_num)).trans hlast))).trans_eq
      (Real.log_exp _)

lemma dilation_cutoff_error_bounds (B : ℝ) (D : ℕ)
    (hB : 0 < B) (hlarge : 4 * Real.log 2 ≤ B ^ (9999 / 10000 : ℝ))
    (hD : (1 / 2 : ℝ) * Real.exp (B ^ (9999 / 10000 : ℝ)) ≤ D) :
    (dilationCutoff B : ℝ) / D ≤ 2 * Real.exp (-B ^ (9999 / 10000 : ℝ) / 8) ∧
      (dilationCutoff B : ℝ) ^ (-(1 / 2) : ℝ) ≤
        2 * Real.exp (-B ^ (9999 / 10000 : ℝ) / 8) := by
  let t := B ^ (9999 / 10000 : ℝ)
  have ht : 0 < t := Real.rpow_pos_of_pos hB _
  have hk := dilationCutoff_bounds B hB hlarge
  have hkp : (0 : ℝ) < dilationCutoff B := by exact_mod_cast hk.1
  have hratio : (dilationCutoff B : ℝ) / D ≤ 2 * Real.exp (-3 * t / 4) := by
    calc
      _ ≤ Real.exp (t / 4) / ((1 / 2 : ℝ) * Real.exp t) :=
        div_le_div₀ (Real.exp_pos _).le hk.2.2 (by positivity) hD
      _ = _ := by
        rw [show -3 * t / 4 = t / 4 - t by ring, Real.exp_sub]
        field_simp
  have hexp : Real.exp (-3 * t / 4) ≤ Real.exp (-t / 8) :=
    Real.exp_le_exp.mpr (by linarith)
  refine ⟨hratio.trans (mul_le_mul_of_nonneg_left hexp (by norm_num)), ?_⟩
  have hlog : t / 4 - Real.log 2 ≤ Real.log (dilationCutoff B : ℝ) := by
    have hh := Real.log_le_log (by positivity : (0 : ℝ) < Real.exp (t / 4) / 2) hk.2.1
    rw [Real.log_div (Real.exp_ne_zero _) (by norm_num), Real.log_exp] at hh
    exact hh
  have hlog2 : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  rw [Real.rpow_def_of_pos hkp]
  calc
    _ ≤ Real.exp (-t / 8 + Real.log 2) := Real.exp_le_exp.mpr (by nlinarith)
    _ = _ := by rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]; ring

structure DilationWindowParameters (B C₀ : ℝ) (D : ℕ) : Prop where
  cutoff_pos : 0 < dilationCutoff B
  cutoff_le : dilationCutoff B ≤ D
  quotient_ten : ∀ a ∈ Icc 1 (dilationCutoff B), 10 ≤ D / a + 1
  quotient_error : ∀ a ∈ Icc 1 (dilationCutoff B),
    Real.log (Real.log (D / a + 1 : ℕ)) / Real.log (D / a + 1 : ℕ) ≤
      (2 * (Real.log (C₀ + 1) + 2)) *
        (Real.log B / B ^ (9999 / 10000 : ℝ))
  cutoff_relative : (dilationCutoff B : ℝ) / D ≤
    2 * (Real.log B / B ^ (9999 / 10000 : ℝ))
  cutoff_tail : (dilationCutoff B : ℝ) ^ (-(1 / 2) : ℝ) ≤
    2 * (Real.log B / B ^ (9999 / 10000 : ℝ))

theorem eventually_dilationWindowParameters (C₀ : ℝ) (hC : 1 ≤ C₀) :
    ∀ᶠ B : ℝ in atTop, ∀ D : ℕ,
      (1 / 2 : ℝ) * Real.exp (B ^ (9999 / 10000 : ℝ)) ≤ D →
      (D : ℝ) ≤ Real.exp (C₀ * B ^ (2 : ℕ)) →
      DilationWindowParameters B C₀ D := by
  have htend := tendsto_rpow_atTop (show 0 < (9999 / 10000 : ℝ) by norm_num)
  have hsmall := htend.eventually
    ((isLittleO_exp_neg_mul_rpow_atTop (show 0 < (1 / 8 : ℝ) by norm_num) (-1)).bound
      (show 0 < (1 : ℝ) by norm_num))
  filter_upwards [eventually_ge_atTop (Real.exp 1),
    htend.eventually (eventually_ge_atTop (4 * Real.log 2)),
    htend.eventually (eventually_ge_atTop (2 * Real.log 10)), hsmall] with
    B hB hlarge hten hsmallB
  intro D hD hDupper
  have hB1 : 1 ≤ B := (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)).trans hB
  have hBp : 0 < B := zero_lt_one.trans_le hB1
  have ht : 0 < B ^ (9999 / 10000 : ℝ) := Real.rpow_pos_of_pos hBp _
  have hlogB : 1 ≤ Real.log B := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hB
  have hlog2 : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  have hK := dilationCutoff_bounds B hBp hlarge
  have hDpos : 0 < D := by
    have hh : (0 : ℝ) < D := lt_of_lt_of_le (by positivity) hD
    exact_mod_cast hh
  have hKD : dilationCutoff B ≤ D := by
    have he : Real.exp (B ^ (9999 / 10000 : ℝ) / 4) ≤
        (1 / 2 : ℝ) * Real.exp (B ^ (9999 / 10000 : ℝ)) := by
      apply (Real.log_le_log_iff (Real.exp_pos _) (by positivity)).mp
      rw [Real.log_exp, Real.log_mul (by norm_num : (1 / 2 : ℝ) ≠ 0)
        (Real.exp_ne_zero _), one_div, Real.log_inv, Real.log_exp]
      linarith
    exact_mod_cast hK.2.2.trans (he.trans hD)
  have hsmall' : Real.exp (-B ^ (9999 / 10000 : ℝ) / 8) ≤
      Real.log B / B ^ (9999 / 10000 : ℝ) := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.norm_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos ht _), one_mul, Real.rpow_neg_one] at hsmallB
    calc
      _ = Real.exp (-(1 / 8 : ℝ) * B ^ (9999 / 10000 : ℝ)) := by congr 1; ring
      _ ≤ (B ^ (9999 / 10000 : ℝ))⁻¹ := hsmallB
      _ ≤ _ := by rw [div_eq_mul_inv]; exact le_mul_of_one_le_left (by positivity) hlogB
  have herr := dilation_cutoff_error_bounds B D hBp hlarge hD
  refine ⟨hK.1, hKD, ?_, ?_,
    herr.1.trans (mul_le_mul_of_nonneg_left hsmall' (by norm_num)),
    herr.2.trans (mul_le_mul_of_nonneg_left hsmall' (by norm_num))⟩
  · intro a ha
    have hm := dilation_quotient_log_lower B D a hBp hlarge hD
      (mem_Icc.mp ha).1 (mem_Icc.mp ha).2
    have hex : (10 : ℝ) ≤ (D / a + 1 : ℕ) := by
      rw [← Real.exp_log (by norm_num : (0 : ℝ) < 10)]
      apply (Real.exp_le_exp.mpr (show Real.log 10 ≤ Real.log (D / a + 1 : ℕ) by linarith)).trans_eq
      exact Real.exp_log (by positivity)
    exact_mod_cast hex
  · intro a ha
    exact quotient_log_error_bound B C₀ (D / a + 1) hB hC
      (dilation_quotient_log_lower B D a hBp hlarge hD (mem_Icc.mp ha).1 (mem_Icc.mp ha).2)
      (dilation_quotient_log_upper B C₀ D a hB1 hDpos hDupper)

end TwoPointCorrelations

end OAI
