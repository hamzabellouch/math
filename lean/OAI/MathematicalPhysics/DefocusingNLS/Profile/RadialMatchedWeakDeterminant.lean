import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedFreeRepresentation
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedWeakCoreLimit
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralGaugeObservation

namespace OAI

/-! A nonzero limiting pencil kernel forces a zero of the certified free determinant. -/

open Set
namespace DefocusingNLS
open ProfileCertificate
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem radialMatchedWeak_nonzero_slowDeterminant_of_boundary (ell : ℕ) (z : ProfileMatchingBall)
    (hz₁ : z.val.1=0) (hz : diskProfile (profileMatchingParameter z)=0)
    (hc : Continuous (radialMatchedFreeMassFunction z)) (R : ℝ)
    (hLR : radialShootingR (profileMatchingParameter z) < R)
    (w : SpectralHarmonicWeight R) (hw : w.density=radialMatchedFreeMassFunction z)
    (ζ : ℂ) (hζ : -(1/32 : ℝ) ≤ ζ.re) (u : SpectralHarmonicPair ell R)
    (hu : u ∈ spectralHarmonicCoreSubspace ell R (radialShootingR (profileMatchingParameter z)))
    (hne : spectralHarmonicObservation ell R ((radialMatchedCore_radius_pos z).trans hLR) u ≠ 0)
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
    (he : let hR := (radialMatchedCore_radius_pos z).trans hLR
      ∀ v : spectralHarmonicCoreSubspace ell R (radialShootingR (profileMatchingParameter z)),
        spectralHarmonicPairComplexForm ell R w u v=
          inner ℂ (radialMatchedLimitWeakOperator ell z hc R hR ζ B
            (spectralHarmonicObservation ell R hR u)) v) :
    spectralSlowDeterminant ell (radialShootingB (profileMatchingParameter z))
      ((radialShootingR (profileMatchingParameter z))^2/4) ζ=0 := by
  let L := radialShootingR (profileMatchingParameter z)
  have hL : 0 < L := radialMatchedCore_radius_pos z
  let hR := hL.trans hLR
  let b := radialShootingB (profileMatchingParameter z)
  let Q := radialShootingFreeExterior z
  obtain ⟨c,hrep⟩ := radialMatchedWeak_free_representation_of_boundary ell z hz₁ hz hc R hLR w hw ζ hζ u hdet B hBoundary he
  let Y : ℝ → E₄ := fun r => c.1 • spectralFreePositivePhysical ell b ζ r+
    c.2 • spectralFreeNegativePhysical ell b ζ r
  have hY : ContinuousOn Y (Ico L R) := by
    intro r hr
    have hd := spectralFreeCombination_hasDerivAt b ζ ((ell : ℂ)*((ell : ℂ)+10))
      (spectralFreePositivePhysical ell b ζ) (spectralFreeNegativePhysical ell b ζ) c.1 c.2 r
      (spectralFreePositivePhysical_hasDerivAt ell b ζ hζ r (hL.trans_le hr.1))
      (spectralFreeNegativePhysical_hasDerivAt ell b ζ hζ r (hL.trans_le hr.1))
    exact hd.continuousAt.continuousWithinAt
  have hcore := radialMatchedWeak_physical_core ell z hz₁ hz hc R hLR w hw ζ B u hu he
    Y hY hrep.symm
  by_contra hroot
  have hd : matchingColumnDeterminant
      (spectralFreeCoreBoundary ell L (spectralFreePositivePhysical ell b ζ L))
      (spectralFreeCoreBoundary ell L (spectralFreeNegativePhysical ell b ζ L)) ≠ 0 := by
    rw [spectralFreeNegativePhysical_eq]
    exact fun h => hroot ((spectralFreeCoreBoundary_zero_iff_spectralSlowDeterminant ell b L ζ hL hζ).mp h)
  change spectralFreeCoreBoundary ell L
    (c.1 • spectralFreePositivePhysical ell b ζ L+c.2 • spectralFreeNegativePhysical ell b ζ L)=0 at hcore
  rw [spectralFreeCoreBoundary_linear] at hcore
  obtain ⟨hc1,hc2⟩ := matchingColumn_coefficients_zero _ _ c.1 c.2 hd hcore
  obtain ⟨hf,_,C,hC,_⟩ := radialMatchedWeak_core ell z hc R hLR w hw ζ B u hu he
  apply hne
  apply spectralHarmonicObservation_zero_of_exterior_gauge ell L R hL hLR u Q
    (fun r hr => radialShootingFreeExterior_ne_zero z r hr.1.le) hf C hC
  intro r hr
  rw [hrep hr]
  simp only [hc1,hc2,zero_smul,add_zero]

theorem radialMatchedWeak_nonzero_slowDeterminant (ell : ℕ) (z : ProfileMatchingBall)
    (hz₁ : z.val.1=0) (hz : diskProfile (profileMatchingParameter z)=0)
    (hc : Continuous (radialMatchedFreeMassFunction z)) (R : ℝ)
    (hLR : radialShootingR (profileMatchingParameter z) < R)
    (w : SpectralHarmonicWeight R) (hw : w.density=radialMatchedFreeMassFunction z)
    (ζ : ℂ) (hζ : -(1/32 : ℝ) ≤ ζ.re) (u : SpectralHarmonicPair ell R)
    (hu : u ∈ spectralHarmonicCoreSubspace ell R (radialShootingR (profileMatchingParameter z)))
    (hne : spectralHarmonicObservation ell R ((radialMatchedCore_radius_pos z).trans hLR) u ≠ 0)
    (hdet : spectralValueDet
      (spectralPhysicalValueMap (spectralFreePositivePhysical ell (radialShootingB (profileMatchingParameter z)) ζ R))
      (spectralPhysicalValueMap (spectralFreeNegativePhysical ell (radialShootingB (profileMatchingParameter z)) ζ R)) ≠ 0)
    (he : let hR := (radialMatchedCore_radius_pos z).trans hLR
      let Q := radialShootingFreeExterior z
      let M := spectralJetRobin
        (spectralFreePositivePhysical ell (radialShootingB (profileMatchingParameter z)) ζ R)
        (spectralFreeNegativePhysical ell (radialShootingB (profileMatchingParameter z)) ζ R)
      let B := spectralFluxBoundary R (radialMatchedFreeMassFunction z R)
        (radialMatchedFreeTransportFunction z R) (spectralGaugeRobin (Q R) (deriv Q R) M)
      ∀ v : spectralHarmonicCoreSubspace ell R (radialShootingR (profileMatchingParameter z)),
        spectralHarmonicPairComplexForm ell R w u v=
          inner ℂ (radialMatchedLimitWeakOperator ell z hc R hR ζ B
            (spectralHarmonicObservation ell R hR u)) v) :
    spectralSlowDeterminant ell (radialShootingB (profileMatchingParameter z))
      ((radialShootingR (profileMatchingParameter z))^2/4) ζ=0 := by
  exact radialMatchedWeak_nonzero_slowDeterminant_of_boundary ell z hz₁ hz hc R hLR w hw ζ hζ
    u hu hne hdet (spectralFluxBoundary R (radialMatchedFreeMassFunction z R)
      (radialMatchedFreeTransportFunction z R)
      (spectralGaugeRobin (radialShootingFreeExterior z R) (deriv (radialShootingFreeExterior z) R)
        (spectralJetRobin
          (spectralFreePositivePhysical ell (radialShootingB (profileMatchingParameter z)) ζ R)
          (spectralFreeNegativePhysical ell (radialShootingB (profileMatchingParameter z)) ζ R)))) rfl he

end DefocusingNLS

end OAI
