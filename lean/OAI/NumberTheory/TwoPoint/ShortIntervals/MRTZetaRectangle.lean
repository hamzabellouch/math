import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTSparseContourScale
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTZetaGrowth
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTZetaCompactStrip

namespace OAI

/-! The pole-corrected zeta logarithmic derivative on the entire sparse
Perron rectangle, including bounded heights and points left of one. -/

namespace TwoPointCorrelations

open Complex Filter
open scoped Topology

theorem MRTWeakHurwitzGrowthInput.zeta_sparse_rectangle (h : MRTWeakHurwitzGrowthInput) :
    ∃ C L₀ : ℝ, 0 < C ∧ ∀ L : ℝ, L₀ ≤ L → ∀ s : ℂ,
      1 - L ^ (-(3 / 4 : ℝ)) ≤ s.re → s.re ≤ 2 →
      |s.im| ≤ 4 * Real.exp (2 * L) → s ≠ 1 →
        riemannZeta s ≠ 0 ∧ ‖mrtZetaPoleCorrection s‖ ≤ C * L ^ 2 := by
  obtain ⟨c, C₀, T₀, hc, hC₀, hT₀, hstrip⟩ := h.strip_logderiv
  obtain ⟨C₁, T₁, hC₁, hT₁, hright⟩ := h.zeta_right_growth
  let T := max 2 (max T₀ T₁)
  obtain ⟨a, B, ha, _, hB, hcompact⟩ := mrt_zeta_compact_strip (T + 2)
  have hdecay := (tendsto_rpow_neg_atTop (show (0 : ℝ) < 3 / 4 by norm_num)).eventually
    (gt_mem_nhds (lt_min ha (by norm_num : (0 : ℝ) < 1 / 2)))
  have he := (mrt_sparse_contour_budget hc).and
    (hdecay.and ((eventually_ge_atTop (1 : ℝ)).and (eventually_ge_atTop (Real.log 11))))
  obtain ⟨L₀, hL₀⟩ := eventually_atTop.mp he
  refine ⟨C₀ + 9 * C₁ + B + 1, L₀, by positivity, ?_⟩
  intro L hL s hσ hσ2 ht hs1
  obtain ⟨hbudget, hδ, hL1, hL11⟩ := hL₀ L hL
  have hLa : L ^ (-(3 / 4 : ℝ)) ≤ a := hδ.le.trans (min_le_left _ _)
  have hLh : L ^ (-(3 / 4 : ℝ)) ≤ 1 / 2 := hδ.le.trans (min_le_right _ _)
  have hσh : 1 / 2 ≤ s.re := by linarith
  have hLsq : 1 ≤ L ^ 2 := by nlinarith
  by_cases hheight : T ≤ |s.im|
  · have ht₀ : T₀ ≤ |s.im| := (le_max_left _ _).trans ((le_max_right _ _).trans hheight)
    have ht₁ : T₁ ≤ |s.im| := (le_max_right _ _).trans ((le_max_right _ _).trans hheight)
    have ht₂ : 2 ≤ |s.im| := (le_max_left _ _).trans hheight
    have hpar := hbudget s.im ht
    have hH := mrt_sparse_contour_height hL11 (by linarith) ht
    have hsrep : ((s.re : ℂ) + Complex.I * (s.im : ℂ)) = s := by
      rw [mul_comm]
      exact Complex.re_add_im s
    have hg : riemannZeta s ≠ 0 ∧
        ‖deriv riemannZeta s / riemannZeta s‖ ≤ (C₀ + 9 * C₁) * L ^ 2 := by
      by_cases hsupper : s.re ≤ 1 + mrtVKRadius (2 * s.im) / 16
      · have hh := hstrip 1 (1 : DirichletCharacter ℂ 1) s.im s.re ht₀
          (by linarith [hpar.1]) hsupper
        simp only [DirichletCharacter.LFunction_modOne_eq, hsrep] at hh
        exact ⟨hh.1, hh.2.trans (by
          have hh' := mul_le_mul_of_nonneg_left hpar.2 hC₀.le
          nlinarith [mul_nonneg hC₁.le (sq_nonneg L)])⟩
      · have hσ1 : 1 < s.re := by
          have hr := Real.rpow_pos_of_pos (mrt_VKLog_pos (2 * s.im)) (-(2 / 3 : ℝ))
          change 0 < mrtVKRadius (2 * s.im) at hr
          linarith
        have hh := hright s.re s.im ht₁ hσ1
        rw [Complex.re_add_im] at hh
        refine ⟨riemannZeta_ne_zero_of_one_le_re hσ1.le, hh.trans ?_⟩
        have hH0 := (mrt_VKLog_pos (2 * s.im)).le
        have hh' : (mrtVKLog (2 * s.im)) ^ 2 ≤ 9 * L ^ 2 := by nlinarith
        have hh'' := mul_le_mul_of_nonneg_left hh' hC₁.le
        nlinarith [mul_nonneg hC₀.le (sq_nonneg L)]
    have hi : ‖(s - 1)⁻¹‖ ≤ 1 := by
      rw [norm_inv]
      have hn : 1 ≤ ‖s - 1‖ := by
        have hh := Complex.abs_im_le_norm (s - 1)
        simp only [Complex.sub_im, Complex.one_im, sub_zero] at hh
        linarith
      simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hn
    refine ⟨hg.1, ?_⟩
    unfold mrtZetaPoleCorrection
    have hh := norm_sub_le (-deriv riemannZeta s / riemannZeta s) ((s - 1)⁻¹)
    rw [neg_div, norm_neg] at hh
    rw [neg_div]
    nlinarith [mul_nonneg hB (sq_nonneg L)]
  · have hn : ‖s‖ ≤ T + 2 := by
      have hh := Complex.norm_le_abs_re_add_abs_im s
      rw [abs_of_nonneg (by linarith : 0 ≤ s.re)] at hh
      linarith
    have hh := hcompact s (by linarith) hn hs1
    refine ⟨hh.1, hh.2.trans ?_⟩
    nlinarith [mul_le_mul_of_nonneg_left hLsq hB,
      mul_nonneg hC₀.le (sq_nonneg L), mul_nonneg hC₁.le (sq_nonneg L)]

end TwoPointCorrelations

end OAI
