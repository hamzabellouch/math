import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedKernelDeterminant
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialFreeSpectralClassification

namespace OAI

/-! The actual constrained limiting pencil has only the symmetry spectral
values in the closed counting half-plane. -/

namespace DefocusingNLS
open ProfileCertificate

theorem radialMatchedLimit_kernel_symmetry (hRouche : RectangleRouche)
    (ell : ℕ) (z : ProfileMatchingBall)
    (hz₁ : z.val.1=0) (hz : diskProfile (profileMatchingParameter z)=0)
    (hc : Continuous (radialMatchedFreeMassFunction z)) (R : ℝ)
    (hLR : radialShootingR (profileMatchingParameter z)<R)
    (s : SpectralPenaltyFamily R (radialShootingR (profileMatchingParameter z)))
    (hmass : s.limitWeight.density=radialMatchedFreeMassFunction z)
    (lam : ℂ) (hhalf : -(1/32 : ℝ)≤lam.re)
    (v : SpectralRadialObservationSpace R) (hne : v≠0)
    (hdet : spectralValueDet
      (spectralPhysicalValueMap (spectralFreePositivePhysical ell
        (radialShootingB (profileMatchingParameter z)) lam R))
      (spectralPhysicalValueMap (spectralFreeNegativePhysical ell
        (radialShootingB (profileMatchingParameter z)) lam R))≠0)
    (hv : let hR := (radialMatchedCore_radius_pos z).trans hLR
      let Q := radialShootingFreeExterior z
      let M := spectralJetRobin
        (spectralFreePositivePhysical ell (radialShootingB (profileMatchingParameter z)) lam R)
        (spectralFreeNegativePhysical ell (radialShootingB (profileMatchingParameter z)) lam R)
      let B := spectralFluxBoundary R (radialMatchedFreeMassFunction z R)
        (radialMatchedFreeTransportFunction z R) (spectralGaugeRobin (Q R) (deriv Q R) M)
      s.limitPencil ell (radialMatchedCore_radius_pos z) hLR
        (radialMatchedLimitWeakOperator ell z hc R hR lam B) v=v) :
    (ell=0 ∧ (lam=0 ∨ lam=1)) ∨ (ell=1 ∧ lam=1/2) := by
  exact (radialFree_spectral_zero_iff hRouche (profileMatchingParameter z) hz ell lam hhalf).mp
    (radialMatchedLimit_kernel_slowDeterminant ell z hz₁ hz hc R hLR s hmass lam hhalf
      v hne hdet hv)

end DefocusingNLS

end OAI
