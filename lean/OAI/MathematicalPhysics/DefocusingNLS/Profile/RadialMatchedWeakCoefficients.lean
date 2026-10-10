import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedCoreBoundary

namespace OAI

/-! Equality of the actual limiting operator and its density-based weak form. -/

namespace DefocusingNLS
open ProfileCertificate

theorem radialMatchedLimitWeakOperator_eq (ell : ℕ) (z : ProfileMatchingBall)
    (hc : Continuous (radialMatchedFreeMassFunction z)) (R : ℝ) (hR : 0 < R)
    (w a : SpectralHarmonicWeight R)
    (hw : w.density=radialMatchedFreeMassFunction z)
    (ha : a.density=radialMatchedFreeTransportFunction z)
    (ζ : ℂ) (B : ℂ × ℂ →L[ℂ] ℂ × ℂ) :
    radialMatchedLimitWeakOperator ell z hc R hR ζ B=
      spectralLowerOrderOperator ell R hR (spectralRadialWeightMultiplier R w)
        (spectralRadialWeightMultiplier R a) 6 ζ B := by
  have hm := spectralRadialWeightMultiplier_eq_of_density R w
    (spectralContinuousCoefficient R (radialMatchedFreeMassFunction z) hc) hw
  have ht := spectralRadialWeightMultiplier_eq_of_density R a
    (spectralContinuousCoefficient R (radialMatchedFreeTransportFunction z)
      (continuous_const.mul (continuous_id.mul (continuous_radialAverage _ hc)))) ha
  change spectralLowerOrderOperator ell R hR _ _ 6 ζ B=_
  rw [← hm,← ht]


theorem radialMatchedWeak_equation (ell : ℕ) (z : ProfileMatchingBall)
    (hc : Continuous (radialMatchedFreeMassFunction z)) (R L : ℝ) (hR : 0 < R)
    (w a : SpectralHarmonicWeight R)
    (hw : w.density=radialMatchedFreeMassFunction z)
    (ha : a.density=radialMatchedFreeTransportFunction z)
    (ζ : ℂ) (B : ℂ × ℂ →L[ℂ] ℂ × ℂ) (u : SpectralHarmonicPair ell R)
    (he : ∀ v : spectralHarmonicCoreSubspace ell R L,
      spectralHarmonicPairComplexForm ell R w u v=
        inner ℂ (radialMatchedLimitWeakOperator ell z hc R hR ζ B
          (spectralHarmonicObservation ell R hR u)) v) :
    ∀ v : spectralHarmonicCoreSubspace ell R L,
      spectralHarmonicPairComplexForm ell R w u v=
        inner ℂ (spectralLowerOrderOperator ell R hR
          (spectralRadialWeightMultiplier R w) (spectralRadialWeightMultiplier R a) 6 ζ B
          (spectralHarmonicObservation ell R hR u)) v := by
  intro v
  exact (he v).trans (congrArg
    (fun (K : SpectralRadialObservationSpace R →L[ℂ] SpectralHarmonicPair ell R) =>
      inner ℂ (K (spectralHarmonicObservation ell R hR u)) (v : SpectralHarmonicPair ell R))
    (radialMatchedLimitWeakOperator_eq ell z hc R hR w a hw ha ζ B))

end DefocusingNLS

end OAI
