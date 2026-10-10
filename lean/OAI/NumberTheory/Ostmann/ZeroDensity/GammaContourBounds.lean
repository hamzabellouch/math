import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import OAI.NumberTheory.Ostmann.ZeroDensity.GammaLogDerivativeBound

namespace OAI

/-! # Gamma logarithmic derivatives on the four contour lines -/

namespace Ostmann

open Complex

theorem gamma_not_pole_of_re (z : ℂ) (hz : -1 < z.re) (hne : z.re ≠ 0) :
    ∀ n : ℕ, z ≠ -(n : ℂ) := by
  intro n he
  have hh := congrArg Complex.re he
  cases n with
  | zero => simp at hh; exact hne hh
  | succ n =>
    simp at hh
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith

theorem norm_inv_le_four_of_quarter_re (z : ℂ) (hz : |z.re| = 1 / 4) :
    ‖z⁻¹‖ ≤ 4 := by
  rw [norm_inv]
  have hn : (1 / 4 : ℝ) ≤ ‖z‖ := hz ▸ abs_re_le_norm z
  have hi := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 4) hn
  simpa only [one_div, inv_div, inv_one, mul_one, inv_inv] using hi

theorem gamma_logDeriv_contour_bound : ∃ B : ℝ, 0 < B ∧ ∀ z : ℂ,
    (z.re = -(1 / 4 : ℝ) ∨ z.re = 1 / 4 ∨ z.re = 3 / 4 ∨ z.re = 5 / 4) →
      ‖logDeriv Complex.Gamma z‖ ≤ B * (1 + |z.im|) := by
  obtain ⟨B, hB, hbound⟩ := gamma_logDeriv_strip_bound
  refine ⟨B + 4, by linarith, ?_⟩
  intro z hz
  rcases hz with hz | hz | hz | hz
  · have hp := gamma_not_pole_of_re z (by linarith) (by rw [hz]; norm_num)
    have hrec := Complex.digamma_apply_add_one z hp
    have hb := hbound (z + 1) (by simp; linarith) (by simp; linarith)
    have hi := norm_inv_le_four_of_quarter_re z (by rw [hz]; norm_num)
    have he : logDeriv Complex.Gamma z = logDeriv Complex.Gamma (z + 1) - z⁻¹ := by
      simp only [← Complex.digamma_def]
      rw [hrec]
      ring
    rw [he]
    have hh := (norm_sub_le (logDeriv Complex.Gamma (z + 1)) z⁻¹).trans (add_le_add hb hi)
    simp only [add_im, one_im, add_zero] at hh
    nlinarith [abs_nonneg z.im]
  · have hb := hbound z (by linarith) (by linarith)
    nlinarith [abs_nonneg z.im]
  · have hb := hbound z (by linarith) (by linarith)
    nlinarith [abs_nonneg z.im]
  · have hp := gamma_not_pole_of_re (z - 1) (by simp; linarith) (by simp; linarith)
    have hrec := Complex.digamma_apply_add_one (z - 1) hp
    have hb := hbound (z - 1) (by simp; linarith) (by simp; linarith)
    have hi := norm_inv_le_four_of_quarter_re (z - 1) (by simp; rw [hz]; norm_num)
    have he : logDeriv Complex.Gamma z = logDeriv Complex.Gamma (z - 1) + (z - 1)⁻¹ := by
      simpa only [sub_add_cancel, Complex.digamma_def] using hrec
    rw [he]
    have hh := (norm_add_le (logDeriv Complex.Gamma (z - 1)) (z - 1)⁻¹).trans (add_le_add hb hi)
    simp only [sub_im, one_im, sub_zero] at hh
    nlinarith [abs_nonneg z.im]

end Ostmann

end OAI
