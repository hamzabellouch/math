import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningDerivativeSmall
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningFarGeometry

namespace OAI

/-! The actual momentum satisfies the WKB small-derivative condition throughout
both outer intervals, with explicit cutoffs on the radius and Airy scale. -/

namespace DefocusingNLS

theorem spectralWKB_radial_slope_small (r p g : ℝ) (hr : 0<r)
    (hprod : 2≤r*p) (hbound : g≤4*p^2/r) : g≤2*p^3 := by
  apply hbound.trans
  apply (div_le_iff₀ hr).mpr
  have hh := mul_le_mul_of_nonneg_left hprod (show 0≤2*p^2 by positivity)
  nlinarith

theorem spectralTurning_positive_derivative_small
    (sign h b eta omega gamma r₀ d M r : ℝ)
    (hs : sign^2=1) (heta : 0≤eta) (hr₀ : 2≤r₀) (hd : 0<d) (hM : 32≤M)
    (hr : r₀+M*d≤r)
    (hz : homogeneousSpectralLocalizationFrequency h b eta omega r₀=0)
    (hscale : spectralLiouvilleSlope eta r₀*d^3=1) :
    |spectralLiouvilleSlope eta r|≤
      2*‖spectralLiouvilleMomentum sign h b eta omega gamma r‖^3 := by
  have hr₀p : 0<r₀ := by linarith
  have hMd : 0<M*d := mul_pos (by linarith) hd
  have hrr : r₀<r := by linarith
  by_cases hnear : r≤2*r₀
  · apply spectralTurning_near_derivative_small sign h b eta omega gamma r₀ d M r
      hs heta hr₀p hd hM (by linarith) hnear _ hz hscale
    rw [abs_of_pos (sub_pos.2 hrr)]
    linarith
  · let F := homogeneousSpectralLocalizationFrequency h b eta omega r
    let p := ‖spectralLiouvilleMomentum sign h b eta omega gamma r‖
    have hfar : 2*r₀≤r := le_of_not_ge hnear
    have hrp : 0<r := hr₀p.trans hrr
    obtain ⟨hFlo,hFg⟩ := spectralTurning_far_geometry h b eta omega r₀ r heta hr₀p hfar hz
    have hn : p^2=‖spectralWKBSquaredMomentum sign F gamma‖ := spectralComplexSqrt_norm_sq _
    have habs : |F|≤p^2 := by rw [hn]; exact spectralWKBSquaredMomentum_norm_lower sign F gamma hs
    have hFp : F≤p^2 := (le_abs_self F).trans habs
    have hp0 : 0≤p := norm_nonneg _
    have hpr : r/8≤p := by nlinarith
    have hprod : 2≤r*p := by
      have hh := mul_le_mul_of_nonneg_left hpr hrp.le
      nlinarith
    have hgr : 0≤ spectralLiouvilleSlope eta r := by dsimp only [spectralLiouvilleSlope]; positivity
    rw [abs_of_nonneg hgr]
    exact spectralWKB_radial_slope_small r p _ hrp hprod
      (hFg.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hFp (by norm_num)) hrp.le))

theorem spectralTurning_negative_derivative_small
    (sign h b eta omega gamma r₀ d M R r : ℝ)
    (hs : sign^2=1) (heta : 0≤eta) (hr₀ : 0<r₀) (hd : 0<d) (hM : 32≤M)
    (hR : 0<R) (hlarge : 16≤r₀*R) (hRr : R≤r) (hr : r≤r₀-M*d)
    (hz : homogeneousSpectralLocalizationFrequency h b eta omega r₀=0)
    (hscale : spectralLiouvilleSlope eta r₀*d^3=1) :
    |spectralLiouvilleSlope eta r|≤
      2*‖spectralLiouvilleMomentum sign h b eta omega gamma r‖^3 := by
  have hMd : 0<M*d := mul_pos (by linarith) hd
  have hrr : r<r₀ := by linarith
  by_cases hnear : r₀/2≤r
  · apply spectralTurning_near_derivative_small sign h b eta omega gamma r₀ d M r
      hs heta hr₀ hd hM hnear (by linarith) _ hz hscale
    rw [abs_of_neg (sub_neg.2 hrr)]
    linarith
  · let F := homogeneousSpectralLocalizationFrequency h b eta omega r
    let p := ‖spectralLiouvilleMomentum sign h b eta omega gamma r‖
    have hfar : r≤r₀/2 := le_of_not_ge hnear
    have hrp : 0<r := hR.trans_le hRr
    obtain ⟨hFlo,hFg⟩ := spectralTurning_forbidden_far h b eta omega r₀ r heta hr₀ hrp hfar hz
    have hn : p^2=‖spectralWKBSquaredMomentum sign F gamma‖ := spectralComplexSqrt_norm_sq _
    have habs : |F|≤p^2 := by rw [hn]; exact spectralWKBSquaredMomentum_norm_lower sign F gamma hs
    have hFp : -F≤p^2 := (neg_le_abs F).trans habs
    have hp0 : 0≤p := norm_nonneg _
    have hpr : r₀/8≤p := by nlinarith
    have hprod : 2≤r*p := by
      have hh := mul_le_mul_of_nonneg_left hpr hrp.le
      have hhR := mul_le_mul_of_nonneg_left hRr hr₀.le
      nlinarith
    have hgr : 0≤ spectralLiouvilleSlope eta r := by dsimp only [spectralLiouvilleSlope]; positivity
    rw [abs_of_nonneg hgr]
    exact spectralWKB_radial_slope_small r p _ hrp hprod
      (hFg.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hFp (by norm_num)) hrp.le))

end DefocusingNLS

end OAI
