import OAI.NumberTheory.TwoPoint.Bounds.QualitativeSquareWindows
import OAI.NumberTheory.TwoPoint.Bounds.SmoothWindowBound
import Mathlib.Algebra.Order.Floor.Semifield

namespace OAI

/-! The smooth-divisor truncation is far below the original window length.
All surviving quotient windows retain a fixed positive fraction of its
logarithmic length. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

noncomputable def dilationCutoff (B : ℝ) : ℕ :=
  ⌊Real.exp (B ^ (9999 / 10000 : ℝ) / 4)⌋₊

lemma quotient_log_error_bound (B C₀ : ℝ) (M : ℕ)
    (hB : Real.exp 1 ≤ B) (hC : 1 ≤ C₀)
    (hlo : B ^ (9999 / 10000 : ℝ) / 2 ≤ Real.log (M : ℝ))
    (hhi : Real.log (M : ℝ) ≤ (C₀ + 1) * B ^ (2 : ℕ)) :
    Real.log (Real.log (M : ℝ)) / Real.log M ≤
      (2 * (Real.log (C₀ + 1) + 2)) *
        (Real.log B / B ^ (9999 / 10000 : ℝ)) := by
  have hB1 : 1 ≤ B := (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)).trans hB
  have hBp : 0 < B := zero_lt_one.trans_le hB1
  have hlogB : 1 ≤ Real.log B := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hB
  have hCpos : 0 < C₀ + 1 := by linarith
  have hClog : 0 ≤ Real.log (C₀ + 1) := Real.log_nonneg (by linarith)
  have hA : 0 < B ^ (9999 / 10000 : ℝ) := Real.rpow_pos_of_pos hBp _
  have hM : 0 < Real.log (M : ℝ) := lt_of_lt_of_le (by positivity) hlo
  have hnum : Real.log (Real.log (M : ℝ)) ≤
      (Real.log (C₀ + 1) + 2) * Real.log B := by
    have hh := Real.log_le_log hM hhi
    rw [Real.log_mul hCpos.ne' (pow_ne_zero 2 hBp.ne'), Real.log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    nlinarith [mul_nonneg hClog (sub_nonneg.mpr hlogB)]
  calc
    _ ≤ ((Real.log (C₀ + 1) + 2) * Real.log B) / Real.log M :=
      div_le_div_of_nonneg_right hnum hM.le
    _ ≤ ((Real.log (C₀ + 1) + 2) * Real.log B) /
        (B ^ (9999 / 10000 : ℝ) / 2) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hlo
    _ = _ := by ring

lemma dilationCutoff_bounds (B : ℝ)
    (_hB : 0 < B) (hlarge : 4 * Real.log 2 ≤ B ^ (9999 / 10000 : ℝ)) :
    0 < dilationCutoff B ∧
      Real.exp (B ^ (9999 / 10000 : ℝ) / 4) / 2 ≤ dilationCutoff B ∧
      (dilationCutoff B : ℝ) ≤ Real.exp (B ^ (9999 / 10000 : ℝ) / 4) := by
  have he : 2 ≤ Real.exp (B ^ (9999 / 10000 : ℝ) / 4) := by
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    exact Real.exp_le_exp.mpr (by linarith)
  have hlo := Nat.lt_floor_add_one (Real.exp (B ^ (9999 / 10000 : ℝ) / 4))
  have hhi := Nat.floor_le (le_of_lt (Real.exp_pos (B ^ (9999 / 10000 : ℝ) / 4)))
  change Real.exp (B ^ (9999 / 10000 : ℝ) / 4) < (dilationCutoff B : ℝ) + 1 at hlo
  change (dilationCutoff B : ℝ) ≤ _ at hhi
  refine ⟨?_, by linarith, hhi⟩
  have hh : (0 : ℝ) < dilationCutoff B := by linarith
  exact_mod_cast hh

lemma dilation_quotient_log_lower (B : ℝ) (D a : ℕ)
    (hB : 0 < B) (hlarge : 4 * Real.log 2 ≤ B ^ (9999 / 10000 : ℝ))
    (hD : (1 / 2 : ℝ) * Real.exp (B ^ (9999 / 10000 : ℝ)) ≤ D)
    (ha : 0 < a) (haK : a ≤ dilationCutoff B) :
    B ^ (9999 / 10000 : ℝ) / 2 ≤ Real.log (D / a + 1 : ℕ) := by
  let t := B ^ (9999 / 10000 : ℝ)
  have hap : (0 : ℝ) < a := by exact_mod_cast ha
  have haKr : (a : ℝ) ≤ dilationCutoff B := by exact_mod_cast haK
  have haexp : (a : ℝ) ≤ Real.exp (t / 4) :=
    haKr.trans (dilationCutoff_bounds B hB hlarge).2.2
  have hr : (1 / 2 : ℝ) * Real.exp (3 * t / 4) ≤ (D : ℝ) / a := by
    calc
      _ = ((1 / 2 : ℝ) * Real.exp t) / Real.exp (t / 4) := by
        calc
          _ = (1 / 2 : ℝ) * Real.exp (t - t / 4) := by congr 2; ring
          _ = (1 / 2 : ℝ) * (Real.exp t / Real.exp (t / 4)) := by rw [Real.exp_sub]
          _ = _ := by ring
      _ ≤ (D : ℝ) / a := div_le_div₀ (by positivity) hD hap haexp
  have hfloor : (D : ℝ) / a < (D / a + 1 : ℕ) := by
    have hh := Nat.lt_floor_add_one ((D : ℝ) / a)
    simpa only [Nat.floor_div_natCast, Nat.floor_natCast, Nat.cast_add, Nat.cast_one] using hh
  have hM : (0 : ℝ) < (D / a + 1 : ℕ) := by positivity
  have hh := Real.log_le_log (by positivity : (0 : ℝ) <
    (1 / 2 : ℝ) * Real.exp (3 * t / 4)) (hr.trans hfloor.le)
  rw [Real.log_mul (by norm_num : (1 / 2 : ℝ) ≠ 0) (Real.exp_ne_zero _),
    Real.log_exp, one_div, Real.log_inv] at hh
  change t / 2 ≤ _
  change 4 * Real.log 2 ≤ t at hlarge
  linarith

end TwoPointCorrelations

end OAI
