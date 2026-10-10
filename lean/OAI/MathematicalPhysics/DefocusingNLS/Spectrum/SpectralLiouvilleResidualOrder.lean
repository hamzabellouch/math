import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralLiouvilleResidualContinuity

namespace OAI

/-! Shrinking a forbidden interval decreases its nonnegative scaled residual integral. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem spectralLiouvilleResidual_unscaled_mono (sign h b eta omega gamma R L E : ℝ)
    (hs : sign^2 = 1) (hR : 0 < R) (hRL : R ≤ L) (hLE : L ≤ E)
    (hF : ∀ t ∈ Icc R E, 0 < sign*homogeneousSpectralLocalizationFrequency h b eta omega t) :
    (∫ t in L..E, ‖spectralLiouvilleResidual sign h b eta omega gamma t‖/
      ‖spectralLiouvilleMomentum sign h b eta omega gamma t‖) ≤
    ∫ t in R..E, ‖spectralLiouvilleResidual sign h b eta omega gamma t‖/
      ‖spectralLiouvilleMomentum sign h b eta omega gamma t‖ := by
  have hc := (spectralLiouvilleResidual_continuousOn sign h b eta omega gamma R E
    hs hR hF).2
  have hi := hc.intervalIntegrable_of_Icc (μ := volume) (hRL.trans hLE)
  exact intervalIntegral.integral_mono_interval hRL hLE le_rfl
    (Filter.Eventually.of_forall (fun _ => by positivity)) hi

theorem spectralLiouvilleResidual_interval_mono (sign h b eta omega gamma R L E : ℝ)
    (hs : sign^2 = 1) (hR : 0 < R) (hRL : R ≤ L) (hLE : L ≤ E)
    (hF : ∀ t ∈ Icc R E, 0 < sign*homogeneousSpectralLocalizationFrequency h b eta omega t) :
    (∫ t in L..E, (25/4 : ℝ)*‖spectralLiouvilleResidual sign h b eta omega gamma t‖/
      ‖spectralLiouvilleMomentum sign h b eta omega gamma t‖) ≤
    ∫ t in R..E, (25/4 : ℝ)*‖spectralLiouvilleResidual sign h b eta omega gamma t‖/
      ‖spectralLiouvilleMomentum sign h b eta omega gamma t‖ := by
  have hc := (spectralLiouvilleResidual_continuousOn sign h b eta omega gamma R E
    hs hR hF).2.const_mul (25/4 : ℝ)
  have hi := hc.intervalIntegrable_of_Icc (μ := volume) (hRL.trans hLE)
  simp only [← mul_div_assoc] at hi
  exact intervalIntegral.integral_mono_interval hRL hLE le_rfl
    (Filter.Eventually.of_forall (fun _ => by positivity)) hi

theorem spectralLiouvilleResidual_integral_mono (h b eta omega gamma R L E : ℝ)
    (hR : 0 < R) (hRL : R ≤ L) (hLE : L ≤ E)
    (hF : ∀ t ∈ Icc R E, 0 < (-1)*homogeneousSpectralLocalizationFrequency h b eta omega t) :
    (∫ t in L..E, (25/4 : ℝ)*‖spectralLiouvilleResidual (-1) h b eta omega gamma t‖/
      ‖spectralLiouvilleMomentum (-1) h b eta omega gamma t‖) ≤
    ∫ t in R..E, (25/4 : ℝ)*‖spectralLiouvilleResidual (-1) h b eta omega gamma t‖/
      ‖spectralLiouvilleMomentum (-1) h b eta omega gamma t‖ := by
  have hc := (spectralLiouvilleResidual_continuousOn (-1) h b eta omega gamma R E
    (by norm_num) hR hF).2.const_mul (25/4 : ℝ)
  have hi := hc.intervalIntegrable_of_Icc (μ := volume) (hRL.trans hLE)
  simp only [← mul_div_assoc] at hi
  exact intervalIntegral.integral_mono_interval hRL hLE le_rfl
    (Filter.Eventually.of_forall (fun _ => by positivity)) hi

end DefocusingNLS

end OAI
