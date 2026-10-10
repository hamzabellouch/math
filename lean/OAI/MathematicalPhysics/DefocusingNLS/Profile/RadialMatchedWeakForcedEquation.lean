import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedWeakCoefficients

namespace OAI

/-! Exact coefficient identification also preserves the first-chain load. -/

namespace DefocusingNLS
open ProfileCertificate

theorem radialMatchedWeak_forced_equation (ell : ℕ) (z : ProfileMatchingBall)
    (hc : Continuous (radialMatchedFreeMassFunction z)) (R L : ℝ) (hR : 0 < R)
    (w a : SpectralHarmonicWeight R)
    (hw : w.density=radialMatchedFreeMassFunction z)
    (ha : a.density=radialMatchedFreeTransportFunction z)
    (F : SpectralHarmonicPair ell R) (ζ : ℂ) (B : ℂ × ℂ →L[ℂ] ℂ × ℂ) (u : SpectralHarmonicPair ell R)
    (he : ∀ v : spectralHarmonicCoreSubspace ell R L,
      spectralHarmonicPairComplexForm ell R w u v=
        inner ℂ (radialMatchedLimitWeakOperator ell z hc R hR ζ B
          (spectralHarmonicObservation ell R hR u)+F) v) :
    ∀ v : spectralHarmonicCoreSubspace ell R L,
      spectralHarmonicPairComplexForm ell R w u v=
        inner ℂ (spectralLowerOrderOperator ell R hR
          (spectralRadialWeightMultiplier R w) (spectralRadialWeightMultiplier R a) 6 ζ B
          (spectralHarmonicObservation ell R hR u)+F) v := by
  intro v
  exact (he v).trans (congrArg
    (fun (K : SpectralRadialObservationSpace R →L[ℂ] SpectralHarmonicPair ell R) =>
      inner ℂ (K (spectralHarmonicObservation ell R hR u)+F) (v : SpectralHarmonicPair ell R))
    (radialMatchedLimitWeakOperator_eq ell z hc R hR w a hw ha ζ B))

end DefocusingNLS

end OAI
