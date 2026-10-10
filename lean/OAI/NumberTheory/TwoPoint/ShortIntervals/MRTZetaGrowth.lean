import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTWeakVKStrip
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTWeakVKDerivative
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTZetaRightBound

namespace OAI

/-! A uniform high-height bound on the full right strip. Close to one use
the shrinking disk; farther right the absolutely convergent series suffices.
The bound is independent of the chosen Perron abscissa. -/

namespace TwoPointCorrelations

open Complex Filter
open scoped Topology

theorem MRTWeakHurwitzGrowthInput.zeta_right_growth (h : MRTWeakHurwitzGrowthInput) :
    ∃ C T : ℝ, 0 < C ∧ 0 < T ∧ ∀ σ t : ℝ, T ≤ |t| → 1 < σ →
      ‖deriv riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) /
        riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C * (mrtVKLog (2 * t)) ^ 2 := by
  obtain ⟨C₀, T₀, hC₀, hT₀, hb⟩ := h.logderiv
  obtain ⟨C₁, hC₁, hright⟩ := mrt_zeta_logderiv_right_bound
  refine ⟨16 * C₀ + 16 + C₁, max T₀ 2, by positivity,
    lt_of_lt_of_le hT₀ (le_max_left _ _), ?_⟩
  intro σ t ht hσ
  have ht₀ : T₀ ≤ |t| := (le_max_left _ _).trans ht
  have ht₂ : 2 ≤ |t| := (le_max_right _ _).trans ht
  let H := mrtVKLog (2 * t)
  have hH : 1 ≤ H := by
    have hh : Real.exp 1 ≤ |2 * t| + 3 := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      linarith [Real.exp_one_lt_d9]
    exact (Real.le_log_iff_exp_le (by positivity)).mpr hh
  have hH0 : 0 < H := zero_lt_one.trans_le hH
  have h13 : 1 ≤ H ^ (1 / 3 : ℝ) := Real.one_le_rpow hH (by norm_num)
  have hlog : Real.log H ≤ 3 * H ^ (1 / 3 : ℝ) := by
    have hh := Real.log_le_rpow_div hH0.le (by norm_num : (0 : ℝ) < 1 / 3)
    linarith
  have hweight : mrtVKWeight 1 (2 * t) ≤ 4 * H ^ (1 / 3 : ℝ) := by
    simp only [mrtVKWeight, Nat.cast_one, Real.log_one, add_zero]
    dsimp only [H] at hlog h13
    linarith
  have hw0 : 0 ≤ mrtVKWeight 1 (2 * t) := zero_le_one.trans (mrt_VKWeight_ge_one (q := 1) hH)
  have hpower : (H ^ (1 / 3 : ℝ)) ^ 2 * H ^ (2 / 3 : ℝ) ≤ H ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hH0.le, ← Real.rpow_add hH0]
    norm_num only [Nat.cast_ofNat]
    rw [← Real.rpow_two]
    exact Real.rpow_le_rpow_of_exponent_le hH (by norm_num)
  have hsmall : H ^ (2 / 3 : ℝ) ≤ H ^ 2 := by
    rw [← Real.rpow_two]
    exact Real.rpow_le_rpow_of_exponent_le hH (by norm_num)
  by_cases hs : σ ≤ 1 + mrtVKRadius (2 * t) / 16
  · have hh := hb 1 (1 : DirichletCharacter ℂ 1) t σ ht₀ hσ hs
    simp only [DirichletCharacter.LFunction_modOne_eq] at hh
    rw [mul_comm Complex.I (t : ℂ)] at hh
    apply hh.trans
    have hw : (mrtVKWeight 1 (2 * t)) ^ 2 ≤ 16 * (H ^ (1 / 3 : ℝ)) ^ 2 := by
      nlinarith [sq_nonneg (4 * H ^ (1 / 3 : ℝ) - mrtVKWeight 1 (2 * t))]
    have hb' := mul_le_mul_of_nonneg_right hw (Real.rpow_nonneg hH0.le (2 / 3 : ℝ))
    dsimp only [H] at hpower hsmall
    nlinarith [mul_le_mul_of_nonneg_left hpower hC₀.le, sq_nonneg (mrtVKLog (2 * t))]
  · have hh := hright (σ - 1) t (by linarith)
    have he : (1 + (σ - 1) : ℝ) = σ := by ring
    rw [he] at hh
    have hinv : 1 / (σ - 1) ≤ 16 * H ^ (2 / 3 : ℝ) := by
      have hr : 0 < mrtVKRadius (2 * t) := Real.rpow_pos_of_pos hH0 _
      have hh' : mrtVKRadius (2 * t) / 16 ≤ σ - 1 := by linarith
      apply (one_div_le_one_div_of_le (div_pos hr (by norm_num)) hh').trans_eq
      dsimp only [mrtVKRadius, H]
      rw [one_div, inv_div, Real.rpow_neg (mrt_VKLog_pos (2 * t)).le,
        div_eq_mul_inv, inv_inv]
    have hHsq : 1 ≤ H ^ 2 := by nlinarith
    dsimp only [H] at hsmall hHsq
    nlinarith [mul_le_mul_of_nonneg_left hsmall (by norm_num : (0 : ℝ) ≤ 16),
      mul_le_mul_of_nonneg_left hHsq hC₁.le,
      mul_nonneg (show 0 ≤ 16 * C₀ by positivity) (sq_nonneg (mrtVKLog (2 * t)))]

end TwoPointCorrelations

end OAI
