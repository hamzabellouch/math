import Mathlib.Analysis.SpecialFunctions.Log.Basic
import OAI.NumberTheory.Ostmann.Construction.FiniteIntervalPacking

namespace OAI

/-! # The actual integer length of a short logarithmic window -/

namespace Ostmann

open scoped Classical BigOperators

 theorem sub_le_mul_log_sub {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    y - x ≤ y * (Real.log y - Real.log x) := by
  have h := mul_le_mul_of_nonneg_right (Real.log_le_sub_one_of_pos (div_pos hx hy)) hy.le
  rw [Real.log_div hx.ne' hy.ne'] at h
  field_simp at h
  nlinarith

 theorem log_window_diameter {n m N : ℕ} {x h : ℝ}
    (hn : 1 ≤ n) (hm : 1 ≤ m) (hnN : n ≤ N) (hmN : m ≤ N) (hh : 0 ≤ h)
    (hln : |Real.log n - x| ≤ h) (hlm : |Real.log m - x| ≤ h) :
    |(n : ℝ) - m| ≤ 2 * N * h := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hnR : (n : ℝ) ≤ N := by exact_mod_cast hnN
  have hmR : (m : ℝ) ≤ N := by exact_mod_cast hmN
  have hdn := abs_le.mp hln
  have hdm := abs_le.mp hlm
  rcases le_total (m : ℝ) n with hmn | hnm
  · rw [abs_of_nonneg (sub_nonneg.mpr hmn)]
    have hlog : Real.log n - Real.log m ≤ 2 * h := by linarith
    have hl := sub_le_mul_log_sub hmpos hnpos
    have hprod := mul_le_mul_of_nonneg_left hlog hnpos.le
    have hsize := mul_le_mul_of_nonneg_right hnR (by linarith : 0 ≤ 2 * h)
    nlinarith
  · rw [abs_of_nonpos (sub_nonpos.mpr hnm)]
    have hlog : Real.log m - Real.log n ≤ 2 * h := by linarith
    have hl := sub_le_mul_log_sub hnpos hmpos
    have hprod := mul_le_mul_of_nonneg_left hlog hmpos.le
    have hsize := mul_le_mul_of_nonneg_right hmR (by linarith : 0 ≤ 2 * h)
    nlinarith

 theorem log_window_integer_interval (S : Finset ℕ) (N : ℕ) (x h : ℝ)
    (hh : 0 ≤ h)
    (hS : ∀ n ∈ S, 1 ≤ n ∧ n ≤ N ∧ |Real.log n - x| ≤ h) :
    ∃ J : ℕ, ∀ n ∈ S, J ≤ n ∧ n < J + (⌈2 * N * h⌉₊ + 1) := by
  by_cases hne : S.Nonempty
  · refine ⟨S.min' hne, ?_⟩
    intro n hn
    have hm := hS (S.min' hne) (Finset.min'_mem S hne)
    have hnn := hS n hn
    have hmin := Finset.min'_le S n hn
    refine ⟨hmin, ?_⟩
    have hd := log_window_diameter hnn.1 hm.1 hnn.2.1 hm.2.1 hh hnn.2.2 hm.2.2
    have hc := Nat.le_ceil (2 * (N : ℝ) * h)
    have hb : (n : ℝ) - S.min' hne ≤ ⌈2 * (N : ℝ) * h⌉₊ := (le_abs_self _).trans (hd.trans hc)
    have hi : n ≤ S.min' hne + ⌈2 * (N : ℝ) * h⌉₊ := by exact_mod_cast (by linarith : (n : ℝ) ≤ (S.min' hne : ℝ) + ⌈2 * (N : ℝ) * h⌉₊)
    omega
  · exact ⟨0, by simp [Finset.not_nonempty_iff_eq_empty.mp hne]⟩

end Ostmann

end OAI
