import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedKernelLine
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralSimpleKernelEstimate
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPencilLimit
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCompactKernelLift

namespace OAI

/-! The concrete free compact pencil has a quantitative lower bound on every
fixed complement of a nonzero kernel vector. -/

namespace DefocusingNLS
open ProfileCertificate

noncomputable def radialMatchedFreeBoundary (ell : ℕ) (z : ProfileMatchingBall)
    (R : ℝ) (ζ : ℂ) : ℂ × ℂ →L[ℂ] ℂ × ℂ :=
  spectralFluxBoundary R (radialMatchedFreeMassFunction z R)
    (radialMatchedFreeTransportFunction z R)
    (spectralGaugeRobin (radialShootingFreeExterior z R) (deriv (radialShootingFreeExterior z) R)
      (spectralJetRobin
        (spectralFreePositivePhysical ell (radialShootingB (profileMatchingParameter z)) ζ R)
        (spectralFreeNegativePhysical ell (radialShootingB (profileMatchingParameter z)) ζ R)))

noncomputable def radialMatchedFreePencil (ell : ℕ) (z : ProfileMatchingBall)
    (hc : Continuous (radialMatchedFreeMassFunction z)) (R : ℝ)
    (hLR : radialShootingR (profileMatchingParameter z) < R)
    (s : SpectralPenaltyFamily R (radialShootingR (profileMatchingParameter z)))
    (ζ : ℂ) : SpectralRadialObservationSpace R →L[ℂ] SpectralRadialObservationSpace R :=
  s.limitPencil ell (radialMatchedCore_radius_pos z) hLR
    (radialMatchedLimitWeakOperator ell z hc R ((radialMatchedCore_radius_pos z).trans hLR)
      ζ (radialMatchedFreeBoundary ell z R ζ))

theorem radialMatchedFreePencil_kernel_line (ell : ℕ) (z : ProfileMatchingBall)
    (hz₁ : z.val.1 = 0) (hz : diskProfile (profileMatchingParameter z) = 0)
    (hc : Continuous (radialMatchedFreeMassFunction z)) (R : ℝ)
    (hLR : radialShootingR (profileMatchingParameter z) < R)
    (s : SpectralPenaltyFamily R (radialShootingR (profileMatchingParameter z)))
    (hmass : s.limitWeight.density = radialMatchedFreeMassFunction z)
    (ζ : ℂ) (hζ : -(1/32 : ℝ) ≤ ζ.re)
    (hdet : spectralValueDet
      (spectralPhysicalValueMap (spectralFreePositivePhysical ell (radialShootingB (profileMatchingParameter z)) ζ R))
      (spectralPhysicalValueMap (spectralFreeNegativePhysical ell (radialShootingB (profileMatchingParameter z)) ζ R)) ≠ 0)
    (v₀ v : SpectralRadialObservationSpace R) (hv₀ : v₀ ≠ 0)
    (hfix₀ : radialMatchedFreePencil ell z hc R hLR s ζ v₀ = v₀)
    (hfix : radialMatchedFreePencil ell z hc R hLR s ζ v = v) :
    ∃ a : ℂ, v = a • v₀ := by
  let hR := (radialMatchedCore_radius_pos z).trans hLR
  let B : ℂ × ℂ →L[ℂ] ℂ × ℂ := radialMatchedFreeBoundary ell z R ζ
  let K : SpectralRadialObservationSpace R →L[ℂ] SpectralHarmonicPair ell R :=
    radialMatchedLimitWeakOperator ell z hc R hR ζ B
  change s.limitPencil ell (radialMatchedCore_radius_pos z) hLR K v₀ = v₀ at hfix₀
  change s.limitPencil ell (radialMatchedCore_radius_pos z) hLR K v = v at hfix
  obtain ⟨u₀, hu₀, ho₀, he₀⟩ :=
    s.limitPencil_kernel_lift ell (radialMatchedCore_radius_pos z) hLR K v₀ hfix₀
  obtain ⟨u, hu, ho, he⟩ :=
    s.limitPencil_kernel_lift ell (radialMatchedCore_radius_pos z) hLR K v hfix
  obtain ⟨a, ha⟩ := radialMatchedWeak_observation_line ell z hz₁ hz hc R hLR
    s.limitWeight hmass ζ hζ u₀ u hu₀ hu (by simpa only [ho₀] using hv₀)
    hdet B rfl he₀ he
  exact ⟨a, by simpa only [ho, ho₀] using ha⟩

theorem radialMatchedFreePencil_complement_estimate (ell : ℕ) (z : ProfileMatchingBall)
    (hz₁ : z.val.1 = 0) (hz : diskProfile (profileMatchingParameter z) = 0)
    (hc : Continuous (radialMatchedFreeMassFunction z)) (R : ℝ)
    (hLR : radialShootingR (profileMatchingParameter z) < R)
    (s : SpectralPenaltyFamily R (radialShootingR (profileMatchingParameter z)))
    (hmass : s.limitWeight.density = radialMatchedFreeMassFunction z)
    (ζ : ℂ) (hζ : -(1/32 : ℝ) ≤ ζ.re)
    (hdet : spectralValueDet
      (spectralPhysicalValueMap (spectralFreePositivePhysical ell (radialShootingB (profileMatchingParameter z)) ζ R))
      (spectralPhysicalValueMap (spectralFreeNegativePhysical ell (radialShootingB (profileMatchingParameter z)) ζ R)) ≠ 0)
    (v₀ : SpectralRadialObservationSpace R)
    (hfix : radialMatchedFreePencil ell z hc R hLR s ζ v₀ = v₀)
    (L : SpectralRadialObservationSpace R →L[ℂ] ℂ) (hL : L v₀ ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ v : SpectralRadialObservationSpace R, L v = 0 →
      c * ‖v‖ ≤ ‖v - radialMatchedFreePencil ell z hc R hLR s ζ v‖ := by
  have hv₀ : v₀ ≠ 0 := by intro h; exact hL (by rw [h, map_zero])
  apply compact_simple_kernel_estimate _
    (s.limitPencil_compact ell (radialMatchedCore_radius_pos z) hLR _) v₀ L hL
  exact fun v hv => radialMatchedFreePencil_kernel_line ell z hz₁ hz hc R hLR s hmass
    ζ hζ hdet v₀ v hv₀ hfix hv

end DefocusingNLS

end OAI
