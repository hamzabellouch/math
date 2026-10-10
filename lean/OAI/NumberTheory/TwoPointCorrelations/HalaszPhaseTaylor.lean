import OAI.NumberTheory.TwoPointCorrelations.HalaszPrimeOscillation
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

namespace OAI

/-! Local phase expansion for the elementary near-twist sum comparison.
The linear term cancels on intervals centered at an integer. -/

namespace TwoPointCorrelations

open scoped ComplexConjugate

lemma halasz_log_one_add_small (u : ℝ) (hu : |u| ≤ 1 / 2) :
    |Real.log (1 + u) - u| ≤ u ^ 2 ∧ |Real.log (1 + u)| ≤ 3 / 2 * |u| := by
  have hp : 0 ≤ 1 + u := by linarith [(abs_le.mp hu).1]
  have hn : ‖(u : ℂ)‖ ≤ 1 / 2 := by simpa only [Complex.norm_real, Real.norm_eq_abs] using hu
  have he : Complex.log (1 + (u : ℂ)) = (Real.log (1 + u) : ℂ) := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_add, ← Complex.ofReal_log hp]
  have hfirst := Complex.norm_log_one_add_sub_self_le (lt_of_le_of_lt hn (by norm_num))
  have hsecond := Complex.norm_log_one_add_half_le_self hn
  rw [he, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_real, Real.norm_eq_abs] at hfirst
  rw [he, Complex.norm_real, Real.norm_eq_abs, Complex.norm_real, Real.norm_eq_abs] at hsecond
  refine ⟨hfirst.trans ?_, hsecond⟩
  have hi : (1 - |u|)⁻¹ ≤ 2 := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ (by linarith : 0 < 1 - |u|)).mpr
    linarith
  rw [sq_abs]
  nlinarith [mul_le_mul_of_nonneg_left hi (sq_nonneg u)]

lemma halasz_phase_linear_error (t u : ℝ) (hu : |u| ≤ 1 / 2)
    (htu : |t * u| ≤ 1 / 2) :
    ‖Complex.exp (((-t * Real.log (1 + u) : ℝ) : ℂ) * Complex.I) - 1 -
        (((-t * u : ℝ) : ℂ) * Complex.I)‖ ≤ 4 * (t ^ 2 + |t|) * u ^ 2 := by
  obtain ⟨hlog, hsize⟩ := halasz_log_one_add_small u hu
  let a : ℝ := -t * Real.log (1 + u)
  let b : ℝ := -t * u
  have ha : |a| ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left hsize (abs_nonneg t)
    rw [abs_mul] at htu
    dsimp [a]
    rw [abs_mul, abs_neg]
    nlinarith
  have hcn : ‖(a : ℂ) * Complex.I‖ ≤ 1 := by
    simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one] using ha
  have hexp := Complex.norm_exp_sub_one_sub_id_le hcn
  have hab : |a - b| ≤ |t| * u ^ 2 := by
    have he : a - b = -t * (Real.log (1 + u) - u) := by dsimp [a, b]; ring
    rw [he, abs_mul, abs_neg]
    exact mul_le_mul_of_nonneg_left hlog (abs_nonneg t)
  have ha2 : a ^ 2 ≤ 9 / 4 * t ^ 2 * u ^ 2 := by
    have hh := pow_le_pow_left₀ (abs_nonneg (Real.log (1 + u))) hsize 2
    rw [sq_abs, mul_pow, sq_abs] at hh
    have hm := mul_le_mul_of_nonneg_left hh (sq_nonneg t)
    dsimp [a]
    nlinarith
  have hsplit : Complex.exp ((a : ℂ) * Complex.I) - 1 - (b : ℂ) * Complex.I =
      (Complex.exp ((a : ℂ) * Complex.I) - 1 - (a : ℂ) * Complex.I) +
        ((a - b : ℝ) : ℂ) * Complex.I := by push_cast; ring
  change ‖Complex.exp ((a : ℂ) * Complex.I) - 1 - (b : ℂ) * Complex.I‖ ≤ _
  rw [hsplit]
  apply (norm_add_le _ _).trans
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one,
    sq_abs] at hexp ⊢
  have hn : 0 ≤ |t| * u ^ 2 := by positivity
  have hn2 : 0 ≤ t ^ 2 * u ^ 2 := by positivity
  nlinarith

end TwoPointCorrelations

end OAI
