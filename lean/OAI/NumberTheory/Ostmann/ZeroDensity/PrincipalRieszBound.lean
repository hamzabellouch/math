import OAI.NumberTheory.Ostmann.ZeroDensity.PrincipalRieszRectangle
import OAI.NumberTheory.Ostmann.ZeroDensity.ZetaAbsoluteRightBound
import OAI.NumberTheory.Ostmann.ZeroDensity.RieszResidueTruncation

namespace OAI

/-! # The principal Riesz error from the regularized zeta rectangle -/

namespace Ostmann

open Complex MeasureTheory Set
open scoped Interval

theorem zeta_logDeriv_from_regularized (s : ℂ) (hs : s ≠ 1)
    (hz : regularizedZeta s ≠ 0) (δ : ℝ) (hδ : 0 < δ) (hd : δ ≤ ‖s - 1‖) :
    ‖logDeriv riemannZeta s‖ ≤ ‖logDeriv regularizedZeta s‖ + 1 / δ := by
  have hzne : riemannZeta s ≠ 0 := by
    intro he
    apply hz
    rw [regularizedZeta_eq s hs, he, mul_zero]
  have he : logDeriv riemannZeta s = logDeriv regularizedZeta s - (s - 1)⁻¹ := by
    rw [regularizedZeta_logDeriv_off_one s hs hzne]
    ring
  rw [he]
  apply (norm_sub_le _ _).trans
  apply add_le_add le_rfl
  rw [norm_inv, ← one_div]
  exact div_le_div_of_nonneg_left zero_le_one hδ hd

theorem zeta_logDeriv_right_continuous (b : ℝ) (hb : 1 < b) :
    Continuous (fun t : ℝ => -logDeriv riemannZeta (rieszMellinLine b t)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hs : rieszMellinLine b t ≠ 1 := by
    intro he
    have hh := congrArg Complex.re he
    simp only [rieszMellinLine_re, Complex.one_re] at hh
    linarith
  have ha := analyticOn_riemannZeta (rieszMellinLine b t) hs
  have hn := riemannZeta_ne_zero_of_one_le_re (by simpa using hb.le : 1 ≤ (rieszMellinLine b t).re)
  exact (((ha.deriv.div ha hn).neg).continuousAt).comp (rieszMellinLine_continuous b).continuousAt

theorem principalRieszMean_rectangle_bound : ∃ K C : ℝ, 0 < K ∧ 0 < C ∧
    ∀ X a b T M : ℝ, 1 ≤ X → 1 / 2 ≤ a → a < 1 → 1 < b → b ≤ 2 → 0 < T → 0 ≤ M →
      (∀ s ∈ uIcc a b ×ℂ uIcc (-T) T, regularizedZeta s ≠ 0) →
      (∀ s ∈ uIcc a b ×ℂ uIcc (-T) T, ‖logDeriv regularizedZeta s‖ ≤ M) →
      ‖principalRieszMean X - (X / 2 : ℝ)‖ ≤
        K * (M + 1 / (1 - a)) * X ^ a +
        2 * ((M + 1 / T) * X ^ b / T ^ 2) * (b - a) +
        2 * (1 / (b - 1) + C) * X ^ b / T := by
  obtain ⟨K, hK, hleft⟩ := weightedRiesz_left_segment_bound
  obtain ⟨C, hC, hright⟩ := zeta_logDeriv_right_pole_bound
  refine ⟨K, C, hK, hC, ?_⟩
  intro X a b T M hX ha ha1 hb hb2 hT hM hne hbound
  have hXp : 0 < X := by linarith
  have hab : a ≤ b := by linarith
  have hmem (σ t : ℝ) (hσ : σ ∈ Icc a b) (ht : t ∈ Icc (-T) T) :
      (σ : ℂ) + (t : ℂ) * I ∈ uIcc a b ×ℂ uIcc (-T) T := by
    constructor
    · simpa [uIcc_of_le hab] using hσ
    · simpa [uIcc_of_le (show -T ≤ T by linarith)] using ht
  have hlow (t : ℝ) (ht : t ∈ Icc (-T) T) :
      ‖-logDeriv riemannZeta (rieszMellinLine a t)‖ ≤ M + 1 / (1 - a) := by
    have hs : rieszMellinLine a t ≠ 1 := by
      intro he
      have hh := congrArg Complex.re he
      simp only [rieszMellinLine_re, Complex.one_re] at hh
      linarith
    have hd : 1 - a ≤ ‖rieszMellinLine a t - 1‖ := by
      have hh := Complex.abs_re_le_norm (rieszMellinLine a t - 1)
      simpa [abs_of_neg (show a - 1 < 0 by linarith)] using hh
    have hm := hmem a t ⟨le_rfl, hab⟩ ht
    simpa only [norm_neg] using (zeta_logDeriv_from_regularized _ hs (hne _ hm)
      (1 - a) (by linarith) hd).trans (add_le_add (hbound _ hm) le_rfl)
  have hedge (σ t : ℝ) (hσ : σ ∈ Icc a b) (ht : |t| = T) :
      ‖-logDeriv riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤ M + 1 / T := by
    have hi : (((σ : ℂ) + (t : ℂ) * I) - 1).im = t := by simp
    have hd : T ≤ ‖((σ : ℂ) + (t : ℂ) * I) - 1‖ := by
      have hh := Complex.abs_im_le_norm (((σ : ℂ) + (t : ℂ) * I) - 1)
      rwa [hi, ht] at hh
    have hs : (σ : ℂ) + (t : ℂ) * I ≠ 1 := by
      intro he
      rw [he, sub_self, norm_zero] at hd
      linarith
    have hm := hmem σ t hσ (abs_le.mp (le_of_eq ht))
    simpa only [norm_neg] using (zeta_logDeriv_from_regularized _ hs (hne _ hm)
      T hT hd).trans (add_le_add (hbound _ hm) le_rfl)
  have hl := hleft (fun s => -logDeriv riemannZeta s) X a T (M + 1 / (1 - a))
    hXp ha (by positivity) hlow
  have hl' : ‖∫ t in -T..T, principalRieszContour X ((a : ℂ) + (t : ℂ) * I)‖ ≤
      K * (M + 1 / (1 - a)) * X ^ a := by
    simpa only [intervalIntegral.integral_of_le (show -T ≤ T by linarith),
      integral_Icc_eq_integral_Ioc, principalRieszContour, rieszContourWeight,
      rieszVerticalWeight, rieszMellinLine] using hl
  have hu := weightedRiesz_horizontal_segment_bound (fun s => -logDeriv riemannZeta s)
    X a b T (M + 1 / T) hX hab (by simpa [abs_of_pos hT]) (by positivity)
    (fun σ hσ => hedge σ T hσ (abs_of_pos hT))
  have hd := weightedRiesz_horizontal_segment_bound (fun s => -logDeriv riemannZeta s)
    X a b (-T) (M + 1 / T) hX hab (by simpa [abs_neg, abs_of_pos hT]) (by positivity)
    (fun σ hσ => hedge σ (-T) hσ (by rw [abs_neg, abs_of_pos hT]))
  rw [neg_sq] at hd
  have hr := principalRieszContour_rectangle X hXp a b (-T) T (by linarith) ha1 hb
    (by linarith) hT hne
  have hr' : rectangleBoundaryIntegral (principalRieszContour X) a b (-T) T =
      I * (((2 * Real.pi : ℝ) : ℂ) * (X / 2 : ℝ)) := by
    rw [hr]
    push_cast
    ring
  have hv := rectangle_vertical_shift_residue_norm_bound _ a b (-T) T _ hr'
  have hrightBound (t : ℝ) : ‖-logDeriv riemannZeta (rieszMellinLine b t)‖ ≤ 1 / (b - 1) + C := by
    simpa only [norm_neg, rieszMellinLine_re] using hright (rieszMellinLine b t) (by simpa using hb) (by simpa using hb2)
  have ht := riesz_residue_truncation (fun s => -logDeriv riemannZeta s) X b
    (1 / (b - 1) + C) T (X / 2 : ℝ) hXp hb.le (by positivity) hT
    (zeta_logDeriv_right_continuous b hb) hrightBound
  rw [← principalRieszMean_eq_vertical_logDerivative X b hXp hb] at ht
  change ‖(∫ t in -T..T, principalRieszContour X ((b : ℂ) + (t : ℂ) * I)) - _‖ ≤ _ at hv
  change ‖principalRieszMean X - (X / 2 : ℝ)‖ ≤
    ‖(∫ t in -T..T, principalRieszContour X ((b : ℂ) + (t : ℂ) * I)) -
      ((2 * Real.pi : ℝ) : ℂ) * (X / 2 : ℝ)‖ + _ at ht
  change ‖∫ σ in a..b, principalRieszContour X ((σ : ℂ) + (T : ℂ) * I)‖ ≤ _ at hu
  change ‖∫ σ in a..b, principalRieszContour X ((σ : ℂ) + ((-T : ℝ) : ℂ) * I)‖ ≤ _ at hd
  nlinarith

end Ostmann

end OAI
