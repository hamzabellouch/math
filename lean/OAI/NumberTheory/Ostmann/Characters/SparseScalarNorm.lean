import Mathlib.Analysis.Complex.Basic
import OAI.NumberTheory.Ostmann.Characters.SparseKernelNumerics

namespace OAI

/-! # The scalar block stays positive while retaining its decrease -/

namespace Ostmann

theorem sparse_scalar_norm_bounds (p ε a : ℝ) (b : ℂ) (hp : 100 ≤ p)
    (hε : 0 ≤ ε) (hεsmall : ε ≤ 1 / 1000000)
    (ha0 : -(17 / 20) / p ≤ a)
    (ha1 : a ≤ -(17 / 20) * (1 - ε ^ 2) / p)
    (hb : ‖b‖ ≤ (289 / 100) * ε / p) :
    (19 / 20 : ℝ) ≤ ‖((1 + 2 * a : ℝ) : ℂ) + b‖ ∧
      ‖((1 + 2 * a : ℝ) : ℂ) + b‖ ≤
        1 - (17 / 10) * (1 - ε ^ 2) / p + (289 / 100) * ε / p := by
  have hp0 : 0 < p := by linarith
  have hsmall : ((17 / 10) + (289 / 100) * ε) / p ≤ (1 / 20 : ℝ) := by
    apply (div_le_iff₀ hp0).mpr
    linarith
  have hbase : 0 ≤ 1 + 2 * a := by
    have he : 2 * (-(17 / 20) / p) = -(17 / 10) / p := by ring
    have hdiv : (17 / 10) / p ≤ (1 / 20 : ℝ) := by
      apply le_trans _ hsmall
      apply (div_le_div_iff_of_pos_right hp0).mpr
      linarith
    have hh := mul_le_mul_of_nonneg_left ha0 (by norm_num : (0 : ℝ) ≤ 2)
    rw [he] at hh
    simp only [neg_div] at hh
    linarith
  have hnorm : ‖((1 + 2 * a : ℝ) : ℂ)‖ = 1 + 2 * a := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hbase]
  constructor
  · have hh := norm_add_le (((1 + 2 * a : ℝ) : ℂ) + b) (-b)
    simp only [add_neg_cancel_right, norm_neg, hnorm] at hh
    have he : 2 * (-(17 / 20) / p) = -(17 / 10) / p := by ring
    have hx := mul_le_mul_of_nonneg_left ha0 (by norm_num : (0 : ℝ) ≤ 2)
    rw [he] at hx
    simp only [neg_div] at hx
    rw [add_div] at hsmall
    linarith
  · have hh := norm_add_le (((1 + 2 * a : ℝ) : ℂ)) b
    rw [hnorm] at hh
    have he : 2 * (-(17 / 20) * (1 - ε ^ 2) / p) =
        -(17 / 10) * (1 - ε ^ 2) / p := by ring
    have hx := mul_le_mul_of_nonneg_left ha1 (by norm_num : (0 : ℝ) ≤ 2)
    rw [he] at hx
    simp only [neg_mul, neg_div] at hx
    linarith

end Ostmann

end OAI
