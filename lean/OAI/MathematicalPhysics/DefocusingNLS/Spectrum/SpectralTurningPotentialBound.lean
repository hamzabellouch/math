import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningForbiddenGeometry

namespace OAI

/-! The frequency height on the fixed turning annulus is controlled by its
slope at the turning point. This bounds the near-turning phase integral. -/

namespace DefocusingNLS

theorem spectralTurning_potential_slope_bound (h b eta omega r₀ r : ℝ)
    (heta : 0≤eta) (hr₀ : 0<r₀) (hr : r₀/2≤r) (hr' : r≤2*r₀)
    (hz : homogeneousSpectralLocalizationFrequency h b eta omega r₀=0) :
    |homogeneousSpectralLocalizationFrequency h b eta omega r|≤
      64*(spectralLiouvilleSlope eta r₀)^2 := by
  let F := homogeneousSpectralLocalizationFrequency h b eta omega r
  let g := spectralLiouvilleSlope eta r₀
  have hg : 0<g := by dsimp only [g,spectralLiouvilleSlope]; positivity
  have hrp : 0<r := by linarith
  have hbound : |F|≤8*g*r₀ := by
    rcases le_total r₀ r with hh | hh
    · obtain ⟨hl,hu⟩ := spectralTurningFrequency_growth h b eta omega r₀ r heta hr₀ hh hr' hz
      have hF : 0≤F := (mul_nonneg (div_nonneg hg.le (by norm_num)) (sub_nonneg.2 hh)).trans hl
      rw [abs_of_nonneg hF]
      exact hu.trans (mul_le_mul_of_nonneg_left (by linarith : r-r₀≤r₀) (by positivity))
    · obtain ⟨hl,hu⟩ := spectralTurning_forbidden_growth h b eta omega r₀ r heta hr₀ hr hh hz
      have hF : F≤0 := by
        have hx : 0≤(g/8)*(r₀-r) := mul_nonneg (by positivity) (sub_nonneg.2 hh)
        linarith
      rw [abs_of_nonpos hF]
      exact hu.trans (mul_le_mul_of_nonneg_left (by linarith : r₀-r≤r₀) (by positivity))
  have hrg : r₀≤8*g := by
    have ht : 0≤2*(eta+99/4)/r₀^3 := by positivity
    dsimp only [g,spectralLiouvilleSlope]
    linarith
  exact hbound.trans (by nlinarith [mul_le_mul_of_nonneg_left hrg (show 0≤8*g by positivity)])

end DefocusingNLS

end OAI
