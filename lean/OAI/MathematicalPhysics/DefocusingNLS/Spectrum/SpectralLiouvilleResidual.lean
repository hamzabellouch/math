import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralLiouvilleFrequencyJet

namespace OAI

/-! The exact residual of the complex Liouville momentum is controlled by the
real frequency derivatives, on either side of a turning point. -/

namespace DefocusingNLS

noncomputable def spectralLiouvilleResidual
    (sign h b eta omega gamma r : ℝ) : ℂ :=
  let p := spectralLiouvilleMomentum sign h b eta omega gamma r
  homogeneousSpectralWKBResidual p
    ((sign : ℂ)*(spectralLiouvilleSlope eta r : ℂ)/(2*p))
    ((sign : ℂ)*(spectralLiouvilleSecond eta r : ℂ)/(2*p)-
      ((sign : ℂ)*(spectralLiouvilleSlope eta r : ℂ))^2/(4*p^3))

theorem spectralLiouville_weighted_residual_le
    (sign h b eta omega gamma r : ℝ) (hs : sign^2=1)
    (hF : homogeneousSpectralLocalizationFrequency h b eta omega r≠0) :
    ‖spectralLiouvilleResidual sign h b eta omega gamma r‖/
        ‖spectralLiouvilleMomentum sign h b eta omega gamma r‖≤
      (5/16 : ℝ)*(spectralLiouvilleSlope eta r)^2/
        (Real.sqrt |homogeneousSpectralLocalizationFrequency h b eta omega r|)^5+
      |spectralLiouvilleSecond eta r|/
        (4*(Real.sqrt |homogeneousSpectralLocalizationFrequency h b eta omega r|)^3) := by
  have hk : 0<Real.sqrt |homogeneousSpectralLocalizationFrequency h b eta omega r| :=
    Real.sqrt_pos.2 (abs_pos.2 hF)
  have hsp : |sign|=1 := by nlinarith [sq_abs sign,abs_nonneg sign]
  have hh := spectralWKB_potential_residual_weighted
    (spectralLiouvilleMomentum sign h b eta omega gamma r)
    ((sign : ℂ)*(spectralLiouvilleSlope eta r : ℂ))
    ((sign : ℂ)*(spectralLiouvilleSecond eta r : ℂ))
    (Real.sqrt |homogeneousSpectralLocalizationFrequency h b eta omega r|) hk
    (spectralWKBSqrt_frequency_lower sign
      (homogeneousSpectralLocalizationFrequency h b eta omega r) gamma hs)
  simpa only [spectralLiouvilleResidual,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    hsp,one_mul,sq_abs] using hh

end DefocusingNLS

end OAI
