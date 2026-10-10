import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

namespace OAI

/-! # Recovering sharp positive counts from the integrated count -/

namespace Ostmann

open scoped BigOperators

noncomputable def finiteRieszSum (S : Finset ℕ) (w : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑ n ∈ S, w n * max (x - n) 0

theorem positivePart_step_lower (x y h : ℝ) (hh : 0 ≤ h) :
    (if y ≤ x then h else 0) ≤ max (x + h - y) 0 - max (x - y) 0 := by
  split_ifs with hy
  · rw [max_eq_left (by linarith : 0 ≤ x + h - y), max_eq_left (sub_nonneg.mpr hy)]
    linarith
  · have hm : max (x - y) 0 ≤ max (x + h - y) 0 := max_le_max_right 0 (by linarith)
    linarith

theorem positivePart_step_upper (x y h : ℝ) (hh : 0 ≤ h) :
    max (x + h - y) 0 - max (x - y) 0 ≤ (if y ≤ x + h then h else 0) := by
  split_ifs with hy
  · by_cases hxy : y ≤ x
    · rw [max_eq_left (by linarith : 0 ≤ x + h - y), max_eq_left (sub_nonneg.mpr hxy)]
      linarith
    · rw [max_eq_left (sub_nonneg.mpr hy), max_eq_right (by linarith : x - y ≤ 0)]
      linarith
  · rw [max_eq_right (by linarith : x + h - y ≤ 0), max_eq_right (by linarith : x - y ≤ 0)]
    norm_num

theorem finiteRieszSum_step (S : Finset ℕ) (w : ℕ → ℝ) (x h : ℝ)
    (hh : 0 ≤ h) (hw : ∀ n ∈ S, 0 ≤ w n) :
    h * (∑ n ∈ S.filter (fun n : ℕ => (n : ℝ) ≤ x), w n) ≤
        finiteRieszSum S w (x + h) - finiteRieszSum S w x ∧
      finiteRieszSum S w (x + h) - finiteRieszSum S w x ≤
        h * (∑ n ∈ S.filter (fun n : ℕ => (n : ℝ) ≤ x + h), w n) := by
  have hdiff : finiteRieszSum S w (x + h) - finiteRieszSum S w x =
      ∑ n ∈ S, w n * (max (x + h - n) 0 - max (x - n) 0) := by
    simp only [finiteRieszSum, mul_sub, Finset.sum_sub_distrib]
  rw [hdiff]
  constructor
  · have hb := Finset.sum_le_sum (s := S) (fun n hn =>
      mul_le_mul_of_nonneg_left (positivePart_step_lower x n h hh) (hw n hn))
    simpa only [mul_ite, mul_zero, Finset.sum_filter, Finset.mul_sum, mul_comm] using hb
  · have hb := Finset.sum_le_sum (s := S) (fun n hn =>
      mul_le_mul_of_nonneg_left (positivePart_step_upper x n h hh) (hw n hn))
    simpa only [mul_ite, mul_zero, Finset.sum_filter, Finset.mul_sum, mul_comm] using hb

end Ostmann

end OAI
