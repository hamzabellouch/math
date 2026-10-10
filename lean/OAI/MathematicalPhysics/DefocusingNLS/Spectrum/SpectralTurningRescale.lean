import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningGeometry

namespace OAI

/-! Quantitative convergence of the rescaled potential to the Airy coefficient.
The estimate applies on each fixed rescaled compact interval. -/

namespace DefocusingNLS

theorem spectralTurning_rescaled_error (h b eta omega r₀ d xi : ℝ)
    (hr₀ : 0<r₀) (heta : 0≤eta) (hdelta : |d*xi|≤r₀/2)
    (hzero : homogeneousSpectralLocalizationFrequency h b eta omega r₀=0)
    (hscale : (r₀/8+2*(eta+99/4)/r₀^3)*d^3=1) :
    |d^2*homogeneousSpectralLocalizationFrequency h b eta omega (r₀+d*xi)-xi|≤
      d^4*xi^2*(1/16+16*(eta+99/4)/r₀^4) := by
  have hb := spectralTurningFrequency_remainder_bound h b eta omega r₀ (d*xi)
    hr₀ heta hdelta hzero
  have he : d^2*homogeneousSpectralLocalizationFrequency h b eta omega (r₀+d*xi)-xi=
      d^2*(homogeneousSpectralLocalizationFrequency h b eta omega (r₀+d*xi)-
        (r₀/8+2*(eta+99/4)/r₀^3)*(d*xi)) := by
    linear_combination xi*hscale
  rw [he,abs_mul,abs_of_nonneg (sq_nonneg d)]
  calc
    _ ≤ d^2*((d*xi)^2*(1/16+16*(eta+99/4)/r₀^4)) :=
      mul_le_mul_of_nonneg_left hb (sq_nonneg d)
    _ = _ := by ring

theorem spectralTurning_rescaled_coefficient (eta r₀ d : ℝ)
    (hr₀ : 0<r₀) (hd : 0≤d) (heta : 0≤eta)
    (hscale : (r₀/8+2*(eta+99/4)/r₀^3)*d^3=1) :
    d^4*(1/16+16*(eta+99/4)/r₀^4)≤(17/2)*d/r₀ := by
  have hr3 : 0<r₀^3 := pow_pos hr₀ 3
  have he : (r₀^4/8+2*(eta+99/4))*d^3=r₀^3 := by
    have hh := congrArg (fun x : ℝ => x*r₀^3) hscale
    field_simp at hh
    nlinarith [hh]
  have h₁ : r₀^4*d^3≤8*r₀^3 := by
    nlinarith [mul_nonneg (show 0≤eta+99/4 by linarith) (show 0≤d^3 by positivity)]
  have h₂ : (eta+99/4)*d^3≤r₀^3/2 := by
    nlinarith [mul_nonneg (show 0≤r₀^4 by positivity) (show 0≤d^3 by positivity)]
  have h₁' : r₀^4*d^4≤8*r₀^3*d := by nlinarith [mul_le_mul_of_nonneg_right h₁ hd]
  have h₂' : (eta+99/4)*d^4≤r₀^3*d/2 := by nlinarith [mul_le_mul_of_nonneg_right h₂ hd]
  apply (mul_le_mul_iff_left₀ (show 0<r₀^4 by positivity)).mp
  field_simp
  nlinarith [h₁',h₂']

end DefocusingNLS

end OAI
