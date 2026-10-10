import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousSpectralLocalizationGeometry
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralWKBSquareRootJet

namespace OAI

/-! Momentum jets for the actual scalar Liouville frequency on either side of its turn. -/

namespace DefocusingNLS

noncomputable def spectralLiouvilleSlope (eta r : ℝ) : ℝ :=
  r/8+2*(eta+99/4)/r^3

noncomputable def spectralLiouvilleSecond (eta r : ℝ) : ℝ :=
  1/8-6*(eta+99/4)/r^4

theorem spectralLiouvilleSlope_hasDerivAt (eta r : ℝ) (hr : 0<r) :
    HasDerivAt (spectralLiouvilleSlope eta) (spectralLiouvilleSecond eta r) r := by
  have hd := ((hasDerivAt_id r).div_const 8).add
    ((((hasDerivAt_id r).pow 3).inv (pow_ne_zero 3 hr.ne')).const_mul (2*(eta+99/4)))
  convert hd using 1
  · funext t
    dsimp only [spectralLiouvilleSlope,Pi.add_apply,Pi.inv_apply,Pi.pow_apply,id_eq]
    ring
  · dsimp only [spectralLiouvilleSecond,Pi.pow_apply,id_eq]
    field_simp [hr.ne']
    ring

noncomputable def spectralLiouvilleMomentum (sign h b eta omega gamma r : ℝ) : ℂ :=
  Complex.sqrt (spectralWKBSquaredMomentum sign
    (homogeneousSpectralLocalizationFrequency h b eta omega r) gamma)

theorem spectralLiouvilleMomentum_hasDerivAt (sign h b eta omega gamma r : ℝ)
    (hr : 0<r) (hpos : 0<sign*homogeneousSpectralLocalizationFrequency h b eta omega r) :
    HasDerivAt (spectralLiouvilleMomentum sign h b eta omega gamma)
      ((sign : ℂ)*(spectralLiouvilleSlope eta r : ℂ)/
        (2*spectralLiouvilleMomentum sign h b eta omega gamma r)) r := by
  have hd := ((homogeneousSpectralLocalizationFrequency_hasDerivAt h b eta omega r hr).ofReal_comp.add_const
    (Complex.I*(gamma : ℂ))).const_mul (sign : ℂ)
  exact spectralComplexSqrt_hasDerivAt _ _ r hd
    (by simpa only [spectralWKBSquaredMomentum_re] using hpos)

theorem spectralLiouvilleMomentumSlope_hasDerivAt (sign h b eta omega gamma r : ℝ)
    (hr : 0<r) (hpos : 0<sign*homogeneousSpectralLocalizationFrequency h b eta omega r) :
    HasDerivAt (fun t => (sign : ℂ)*(spectralLiouvilleSlope eta t : ℂ)/
        (2*spectralLiouvilleMomentum sign h b eta omega gamma t))
      ((sign : ℂ)*(spectralLiouvilleSecond eta r : ℂ)/
        (2*spectralLiouvilleMomentum sign h b eta omega gamma r)-
      ((sign : ℂ)*(spectralLiouvilleSlope eta r : ℂ))^2/
        (4*(spectralLiouvilleMomentum sign h b eta omega gamma r)^3)) r := by
  have hd := ((homogeneousSpectralLocalizationFrequency_hasDerivAt h b eta omega r hr).ofReal_comp.add_const
    (Complex.I*(gamma : ℂ))).const_mul (sign : ℂ)
  have he := (spectralLiouvilleSlope_hasDerivAt eta r hr).ofReal_comp.const_mul (sign : ℂ)
  exact spectralComplexSqrt_slope_hasDerivAt _ _ _ r hd he
    (by simpa only [spectralWKBSquaredMomentum_re] using hpos)

end DefocusingNLS

end OAI
