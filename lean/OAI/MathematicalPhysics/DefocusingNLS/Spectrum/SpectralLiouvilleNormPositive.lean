import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralLiouvilleResidual

namespace OAI

/-! Positivity of the actual Liouville Cauchy-state weight away from a turn. -/

namespace DefocusingNLS

theorem spectralLiouville_norm_weight_pos (sign h b eta omega gamma r : ℝ)
    (hs : sign^2=1) (hF : homogeneousSpectralLocalizationFrequency h b eta omega r≠0) :
    0<Real.sqrt ‖spectralLiouvilleMomentum sign h b eta omega gamma r‖ := by
  apply Real.sqrt_pos.2
  exact (Real.sqrt_pos.2 (abs_pos.2 hF)).trans_le
    (spectralWKBSqrt_frequency_lower sign
      (homogeneousSpectralLocalizationFrequency h b eta omega r) gamma hs)

end DefocusingNLS

end OAI
