import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedWeakDeterminant

namespace OAI

/-! The actual compact limiting pencil kernel is detected by the free determinant. -/

namespace DefocusingNLS
open ProfileCertificate

theorem radialMatchedLimit_kernel_slowDeterminant_of_boundary (ell : ℕ) (z : ProfileMatchingBall)
    (hz₁ : z.val.1=0) (hz : diskProfile (profileMatchingParameter z)=0)
    (hc : Continuous (radialMatchedFreeMassFunction z)) (R : ℝ)
    (hLR : radialShootingR (profileMatchingParameter z) < R)
    (s : SpectralPenaltyFamily R (radialShootingR (profileMatchingParameter z)))
    (hmass : s.limitWeight.density=radialMatchedFreeMassFunction z)
    (ζ : ℂ) (hζ : -(1/32 : ℝ) ≤ ζ.re)
    (v : SpectralRadialObservationSpace R) (hne : v ≠ 0)
    (hdet : spectralValueDet
      (spectralPhysicalValueMap (spectralFreePositivePhysical ell (radialShootingB (profileMatchingParameter z)) ζ R))
      (spectralPhysicalValueMap (spectralFreeNegativePhysical ell (radialShootingB (profileMatchingParameter z)) ζ R)) ≠ 0)
    (B : ℂ × ℂ →L[ℂ] ℂ × ℂ)
    (hBoundary : B=spectralFluxBoundary R (radialMatchedFreeMassFunction z R)
      (radialMatchedFreeTransportFunction z R)
      (spectralGaugeRobin (radialShootingFreeExterior z R) (deriv (radialShootingFreeExterior z) R)
        (spectralJetRobin
          (spectralFreePositivePhysical ell (radialShootingB (profileMatchingParameter z)) ζ R)
          (spectralFreeNegativePhysical ell (radialShootingB (profileMatchingParameter z)) ζ R))))
    (hv : let hR := (radialMatchedCore_radius_pos z).trans hLR
      s.limitPencil ell (radialMatchedCore_radius_pos z) hLR
        (radialMatchedLimitWeakOperator ell z hc R hR ζ B) v=v) :
    spectralSlowDeterminant ell (radialShootingB (profileMatchingParameter z))
      ((radialShootingR (profileMatchingParameter z))^2/4) ζ=0 := by
  let hR := (radialMatchedCore_radius_pos z).trans hLR
  obtain ⟨u,hu,hobs,hweak⟩ := (s.limitPencil_complex_variational ell
    (radialMatchedCore_radius_pos z) hLR
    (radialMatchedLimitWeakOperator ell z hc R hR ζ B) v).mp hv
  apply radialMatchedWeak_nonzero_slowDeterminant_of_boundary ell z hz₁ hz hc R hLR s.limitWeight hmass
    ζ hζ u hu (by simpa only [hobs] using hne) hdet B hBoundary
  dsimp only
  intro w
  simpa only [hobs] using hweak w

theorem radialMatchedLimit_kernel_slowDeterminant (ell : ℕ) (z : ProfileMatchingBall)
    (hz₁ : z.val.1=0) (hz : diskProfile (profileMatchingParameter z)=0)
    (hc : Continuous (radialMatchedFreeMassFunction z)) (R : ℝ)
    (hLR : radialShootingR (profileMatchingParameter z) < R)
    (s : SpectralPenaltyFamily R (radialShootingR (profileMatchingParameter z)))
    (hmass : s.limitWeight.density=radialMatchedFreeMassFunction z)
    (ζ : ℂ) (hζ : -(1/32 : ℝ) ≤ ζ.re)
    (v : SpectralRadialObservationSpace R) (hne : v ≠ 0)
    (hdet : spectralValueDet
      (spectralPhysicalValueMap (spectralFreePositivePhysical ell (radialShootingB (profileMatchingParameter z)) ζ R))
      (spectralPhysicalValueMap (spectralFreeNegativePhysical ell (radialShootingB (profileMatchingParameter z)) ζ R)) ≠ 0)
    (hv : let hR := (radialMatchedCore_radius_pos z).trans hLR
      let Q := radialShootingFreeExterior z
      let M := spectralJetRobin
        (spectralFreePositivePhysical ell (radialShootingB (profileMatchingParameter z)) ζ R)
        (spectralFreeNegativePhysical ell (radialShootingB (profileMatchingParameter z)) ζ R)
      let B := spectralFluxBoundary R (radialMatchedFreeMassFunction z R)
        (radialMatchedFreeTransportFunction z R) (spectralGaugeRobin (Q R) (deriv Q R) M)
      s.limitPencil ell (radialMatchedCore_radius_pos z) hLR
        (radialMatchedLimitWeakOperator ell z hc R hR ζ B) v=v) :
    spectralSlowDeterminant ell (radialShootingB (profileMatchingParameter z))
      ((radialShootingR (profileMatchingParameter z))^2/4) ζ=0 := by
  exact radialMatchedLimit_kernel_slowDeterminant_of_boundary ell z hz₁ hz hc R hLR s hmass ζ hζ
    v hne hdet (spectralFluxBoundary R (radialMatchedFreeMassFunction z R)
      (radialMatchedFreeTransportFunction z R)
      (spectralGaugeRobin (radialShootingFreeExterior z R) (deriv (radialShootingFreeExterior z) R)
        (spectralJetRobin
          (spectralFreePositivePhysical ell (radialShootingB (profileMatchingParameter z)) ζ R)
          (spectralFreeNegativePhysical ell (radialShootingB (profileMatchingParameter z)) ζ R)))) rfl hv

theorem radialMatchedLimitPencil_kernel_zero (ell : ℕ) (z : ProfileMatchingBall)
    (hz₁ : z.val.1=0) (hz : diskProfile (profileMatchingParameter z)=0)
    (hc : Continuous (radialMatchedFreeMassFunction z)) (R : ℝ)
    (hLR : radialShootingR (profileMatchingParameter z) < R)
    (s : SpectralPenaltyFamily R (radialShootingR (profileMatchingParameter z)))
    (hmass : s.limitWeight.density=radialMatchedFreeMassFunction z)
    (ζ : ℂ) (hζ : -(1/32 : ℝ) ≤ ζ.re)
    (v : SpectralRadialObservationSpace R)
    (hdet : spectralValueDet
      (spectralPhysicalValueMap (spectralFreePositivePhysical ell (radialShootingB (profileMatchingParameter z)) ζ R))
      (spectralPhysicalValueMap (spectralFreeNegativePhysical ell (radialShootingB (profileMatchingParameter z)) ζ R)) ≠ 0)
    (hD : spectralSlowDeterminant ell (radialShootingB (profileMatchingParameter z))
      ((radialShootingR (profileMatchingParameter z))^2/4) ζ ≠ 0)
    (hv : let hR := (radialMatchedCore_radius_pos z).trans hLR
      let Q := radialShootingFreeExterior z
      let M := spectralJetRobin
        (spectralFreePositivePhysical ell (radialShootingB (profileMatchingParameter z)) ζ R)
        (spectralFreeNegativePhysical ell (radialShootingB (profileMatchingParameter z)) ζ R)
      let B := spectralFluxBoundary R (radialMatchedFreeMassFunction z R)
        (radialMatchedFreeTransportFunction z R) (spectralGaugeRobin (Q R) (deriv Q R) M)
      s.limitPencil ell (radialMatchedCore_radius_pos z) hLR
        (radialMatchedLimitWeakOperator ell z hc R hR ζ B) v=v) : v=0 := by
  by_contra hne
  exact hD (radialMatchedLimit_kernel_slowDeterminant ell z hz₁ hz hc R hLR s hmass
    ζ hζ v hne hdet hv)

end DefocusingNLS

end OAI
