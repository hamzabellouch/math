import OAI.NumberTheory.TwoPoint.Fourier.ModFiveSmoothedContour
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace OAI

/-! Elementary parameter choices for the smoothed Perron bound.  The
height is exp(y) and the original cutoff is exp(y²). -/

namespace TwoPointCorrelations

open Filter

lemma modFive_perron_height {y : ℝ} (hy : 2 ≤ y) :
    2 ≤ Real.exp y ∧ y ≤ Real.log (Real.exp y + 2) ∧
      Real.log (Real.exp y + 2) ≤ 2 * y := by
  have he : 2 ≤ Real.exp y := by linarith [Real.add_one_le_exp y]
  refine ⟨he, ?_, ?_⟩
  · simpa only [Real.log_exp] using
      Real.log_le_log (Real.exp_pos y) (by linarith : Real.exp y ≤ Real.exp y + 2)
  · have hh : Real.exp y + 2 ≤ Real.exp (2 * y) := by
      rw [show 2 * y = y + y by ring, Real.exp_add]
      nlinarith
    simpa only [Real.log_exp] using Real.log_le_log (by positivity) hh

lemma modFive_perron_right_power {y : ℝ} (hy : 0 < y) :
    (Real.exp (y ^ 2)) ^ (1 + 1 / y ^ 2) = Real.exp (y ^ 2 + 1) := by
  rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  congr 1
  field_simp

lemma modFive_perron_left_power {a y H : ℝ} (ha : 0 ≤ a) (hy : 0 < y)
    (hH : 0 < H) (hHle : H ≤ 2 * y) :
    (Real.exp (y ^ 2)) ^ (1 - a / H) ≤ Real.exp (y ^ 2 - a * y / 2) := by
  have hq : y / 2 ≤ y ^ 2 / H := (le_div_iff₀ hH).mpr (by nlinarith)
  have hm := mul_le_mul_of_nonneg_left hq ha
  have he : a * (y ^ 2 / H) = y ^ 2 * (a / H) := by ring
  rw [he] at hm
  rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  apply Real.exp_le_exp.mpr
  nlinarith

lemma modFive_perron_polynomial_absorption (K c : ℝ) (hc : 0 < c) :
    ∀ᶠ y : ℝ in atTop, K * y ^ 2 * Real.exp (1 - c * y) ≤ 1 := by
  have ht := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 2 c hc).const_mul
    (K * Real.exp 1)
  simp only [mul_zero] at ht
  have he : (fun y : ℝ => K * y ^ 2 * Real.exp (1 - c * y)) =
      (fun y : ℝ => (K * Real.exp 1) * (y ^ (2 : ℝ) * Real.exp (-c * y))) := by
    funext y
    rw [Real.rpow_two, show 1 - c * y = 1 + (-c * y) by ring, Real.exp_add]
    ring
  rw [← he] at ht
  exact (ht.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))).mono fun _ h => h.le

end TwoPointCorrelations

end OAI
