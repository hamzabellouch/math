import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedFreeWeakDerivative

namespace OAI

/-! Differentiation of the observed free compact pencil. -/

namespace DefocusingNLS
open ProfileCertificate

noncomputable local instance freePencilDerivativeNormed (R : ℝ) :
    NormedAddCommGroup (SpectralRadialObservationSpace R →L[ℂ] SpectralRadialObservationSpace R) := by
  let : NormedAddCommGroup (SpectralRadialObservationSpace R) := inferInstance
  let : NormedSpace ℂ (SpectralRadialObservationSpace R) := inferInstance
  exact ContinuousLinearMap.toNormedAddCommGroup

theorem radialMatchedFreePencil_hasDerivAt (ell : ℕ) (z : ProfileMatchingBall)
    (hc : Continuous (radialMatchedFreeMassFunction z)) (R : ℝ)
    (hLR : radialShootingR (profileMatchingParameter z) < R)
    (s : SpectralPenaltyFamily R (radialShootingR (profileMatchingParameter z)))
    (hmass : s.limitWeight.density=radialMatchedFreeMassFunction z)
    (lam : ℂ) (hhalf : -(1/32 : ℝ) ≤ lam.re)
    (hdet : spectralValueDet
      (spectralPhysicalValueMap (spectralFreePositivePhysical ell (radialShootingB (profileMatchingParameter z)) lam R))
      (spectralPhysicalValueMap (spectralFreeNegativePhysical ell (radialShootingB (profileMatchingParameter z)) lam R)) ≠ 0) :
    let hL := radialMatchedCore_radius_pos z
    HasDerivAt (radialMatchedFreePencil ell z hc R hLR s)
      (s.limitPencil ell hL hLR (spectralLowerOrderSlope ell R (hL.trans hLR)
        (spectralRadialWeightMultiplier R s.limitWeight)
        (deriv (radialMatchedFreeBoundary ell z R) lam))) lam := by
  have hK := radialMatchedFreeWeak_hasDerivAt ell z hc R hLR s.limitWeight hmass lam hhalf hdet
  exact s.limitPencil_hasDerivAt ell (radialMatchedCore_radius_pos z) hLR _ _ lam hK

end DefocusingNLS

end OAI
