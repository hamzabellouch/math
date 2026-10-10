import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.ENat.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OAI

/-!
# The finite logarithmic profile

The profile is zero at infinite graph distance. Its exact finite expansion
and the factor-three dilation estimate include distances beyond the cutoff.
-/

noncomputable section

namespace MetricEntropyDuality.LogProfile

open scoped BigOperators

/-- The positive logarithmic increment at level `j`. -/
def gamma (h j : ℕ) : ℝ :=
  (Real.log ((j : ℝ) + 2) - Real.log ((j : ℝ) + 1)) / Real.log ((h : ℝ) + 1)

/-- The actual cutoff profile, with a separate value at infinite distance. -/
def phi (h : ℕ) (d : ℕ∞) : ℝ :=
  if d = ⊤ then 0 else
    max 0 (1 - Real.log ((d.toNat : ℝ) + 1) / Real.log ((h : ℝ) + 1))

theorem log_cutoff_pos {h : ℕ} (hh : 0 < h) : 0 < Real.log ((h : ℝ) + 1) := by
  apply Real.log_pos
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  linarith

theorem gamma_pos {h : ℕ} (hh : 0 < h) (j : ℕ) : 0 < gamma h j := by
  unfold gamma
  apply div_pos _ (log_cutoff_pos hh)
  apply sub_pos.mpr
  apply Real.log_lt_log (by positivity)
  linarith

theorem gamma_nonneg {h : ℕ} (hh : 0 < h) (j : ℕ) : 0 ≤ gamma h j :=
  (gamma_pos hh j).le

@[simp] theorem phi_top (h : ℕ) : phi h ⊤ = 0 := by simp [phi]

@[simp] theorem phi_coe (h d : ℕ) :
    phi h (d : ℕ∞) =
      max 0 (1 - Real.log ((d : ℝ) + 1) / Real.log ((h : ℝ) + 1)) := by
  simp [phi]

@[simp] theorem phi_zero (h : ℕ) : phi h 0 = 1 := by simp [phi]

theorem phi_nonneg (h : ℕ) (d : ℕ∞) : 0 ≤ phi h d := by
  unfold phi
  split_ifs
  · exact le_rfl
  · exact le_max_left _ _

theorem phi_le_one {h : ℕ} (hh : 0 < h) (d : ℕ∞) : phi h d ≤ 1 := by
  cases d using ENat.recTopCoe with
  | top => simp
  | coe d =>
      rw [phi_coe]
      apply max_le (by norm_num)
      exact sub_le_self _ (div_nonneg (Real.log_nonneg (by have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d; linarith))
        (log_cutoff_pos hh).le)

theorem phi_eq_zero_of_le {h : ℕ} (hh : 0 < h) {d : ℕ∞}
    (hd : (h : ℕ∞) ≤ d) : phi h d = 0 := by
  cases d using ENat.recTopCoe with
  | top => exact phi_top h
  | coe d =>
      have hhd : h ≤ d := ENat.natCast_le_natCast.mp hd
      have hlog : Real.log ((h : ℝ) + 1) ≤ Real.log ((d : ℝ) + 1) := by
        apply Real.log_le_log (by positivity)
        exact_mod_cast Nat.add_le_add_right hhd 1
      have hratio : 1 ≤ Real.log ((d : ℝ) + 1) / Real.log ((h : ℝ) + 1) :=
        (le_div_iff₀ (log_cutoff_pos hh)).2 (by simpa using hlog)
      rw [phi_coe]
      exact max_eq_left (sub_nonpos.mpr hratio)

/-- Telescoping a tail also handles an empty tail by the minimum endpoint. -/
private theorem sum_log_steps (d h : ℕ) :
    (∑ j ∈ Finset.range h,
      if d ≤ j then Real.log ((j : ℝ) + 2) - Real.log ((j : ℝ) + 1) else 0) =
      Real.log ((h : ℝ) + 1) - Real.log (((min d h : ℕ) : ℝ) + 1) := by
  induction h with
  | zero => simp
  | succ h ih =>
      rw [Finset.sum_range_succ, ih]
      by_cases hd : d ≤ h
      · have hds : d ≤ h + 1 := by omega
        simp only [ite_eq_left hd, min_eq_left hd, min_eq_left hds, Nat.cast_succ]
        rw [show (h : ℝ) + 1 + 1 = (h : ℝ) + 2 by ring]
        ring
      · have hhd : h ≤ d := by omega
        have hhsd : h + 1 ≤ d := by omega
        simp only [ite_eq_right hd, min_eq_right hhd, min_eq_right hhsd, sub_self, add_zero]

private theorem sum_gamma_tail (h d : ℕ) :
    (∑ j ∈ Finset.range h, if d ≤ j then gamma h j else 0) =
      (Real.log ((h : ℝ) + 1) - Real.log (((min d h : ℕ) : ℝ) + 1)) /
        Real.log ((h : ℝ) + 1) := by
  calc
    _ = (∑ j ∈ Finset.range h,
        if d ≤ j then Real.log ((j : ℝ) + 2) - Real.log ((j : ℝ) + 1) else 0) /
          Real.log ((h : ℝ) + 1) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j _
      by_cases hd : d ≤ j <;> simp [hd, gamma]
    _ = _ := by rw [sum_log_steps]

/-- Exact expansion into the finite graph-ball indicators. -/
theorem phi_eq_sum {h : ℕ} (hh : 0 < h) (d : ℕ∞) :
    phi h d = ∑ j ∈ Finset.range h, if d ≤ (j : ℕ∞) then gamma h j else 0 := by
  cases d using ENat.recTopCoe with
  | top => simp
  | coe d =>
      simp only [ENat.natCast_le_natCast]
      rw [sum_gamma_tail]
      by_cases hd : d ≤ h
      · have hlog : Real.log ((d : ℝ) + 1) ≤ Real.log ((h : ℝ) + 1) := by
          apply Real.log_le_log (by positivity)
          exact_mod_cast Nat.add_le_add_right hd 1
        have hratio : Real.log ((d : ℝ) + 1) / Real.log ((h : ℝ) + 1) ≤ 1 :=
          (div_le_one (log_cutoff_pos hh)).2 hlog
        rw [phi_coe, min_eq_left hd, sub_div, div_self (log_cutoff_pos hh).ne',
          max_eq_right (sub_nonneg.mpr hratio)]
      · have hhd : h ≤ d := by omega
        rw [phi_eq_zero_of_le hh (ENat.natCast_le_natCast.mpr hhd), min_eq_right hhd,
          sub_self, zero_div]

theorem sum_gamma {h : ℕ} (hh : 0 < h) :
    (∑ j ∈ Finset.range h, gamma h j) = 1 := by
  simpa using (phi_eq_sum hh 0).symm

theorem phi_eq_sum_mul_indicator {h : ℕ} (hh : 0 < h) (d : ℕ∞) :
    phi h d = ∑ j ∈ Finset.range h,
      gamma h j * (if d ≤ (j : ℕ∞) then (1 : ℝ) else 0) := by
  simpa only [mul_ite, mul_one, mul_zero] using phi_eq_sum hh d

/-- The exact discrete factor-three dilation bound. -/
theorem dilation {h : ℕ} (hh : 0 < h) (d : ℕ∞) :
    (∑ j ∈ Finset.range h,
      if d ≤ ((3 * j + 2 : ℕ) : ℕ∞) then gamma h j else 0) ≤
      phi h d + Real.log 3 / Real.log ((h : ℝ) + 1) := by
  have hL := log_cutoff_pos hh
  have herror : 0 ≤ Real.log 3 / Real.log ((h : ℝ) + 1) :=
    div_nonneg (Real.log_nonneg (by norm_num)) hL.le
  cases d using ENat.recTopCoe with
  | top =>
      simpa only [phi_top, top_le_iff, ENat.natCast_ne_top, ite_false,
        Finset.sum_const_zero, zero_add] using herror
  | coe d =>
      have hsum : (∑ j ∈ Finset.range h,
          if (d : ℕ∞) ≤ ((3 * j + 2 : ℕ) : ℕ∞) then gamma h j else 0) =
          phi h ((d / 3 : ℕ) : ℕ∞) := by
        rw [phi_eq_sum hh]
        apply Finset.sum_congr rfl
        intro j _
        have hdj : d ≤ 3 * j + 2 ↔ d / 3 ≤ j := by omega
        simp only [ENat.natCast_le_natCast, hdj]
      rw [hsum, phi_coe]
      have hd : (d : ℝ) + 1 ≤ 3 * ((d / 3 : ℕ) + 1 : ℝ) := by
        have hdNat : d + 1 ≤ 3 * (d / 3 + 1) := by omega
        exact_mod_cast hdNat
      have hlog := Real.log_le_log (by positivity : 0 < (d : ℝ) + 1) hd
      rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) (by positivity)] at hlog
      have hquot := div_le_div_of_nonneg_right hlog hL.le
      rw [add_div] at hquot
      have hbase : 1 - Real.log ((d : ℝ) + 1) / Real.log ((h : ℝ) + 1) ≤
          phi h (d : ℕ∞) := by
        rw [phi_coe]
        exact le_max_right _ _
      apply max_le (add_nonneg (phi_nonneg _ _) herror)
      linarith

theorem dilation_mul_indicator {h : ℕ} (hh : 0 < h) (d : ℕ∞) :
    (∑ j ∈ Finset.range h,
      gamma h j * (if d ≤ ((3 * j + 2 : ℕ) : ℕ∞) then (1 : ℝ) else 0)) ≤
      phi h d + Real.log 3 / Real.log ((h : ℝ) + 1) := by
  simpa only [mul_ite, mul_one, mul_zero] using dilation hh d

end MetricEntropyDuality.LogProfile

end

end OAI
