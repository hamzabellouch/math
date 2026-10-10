import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedWeakChainPhysical
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedWeakCoefficientTrace
import OAI.MathematicalPhysics.DefocusingNLS.Certificates.FreePhysicalGeneralizedExclusion

namespace OAI

/-! The constrained weak free pencil has no first chain at a symmetry root. -/

open Set
namespace DefocusingNLS
open ProfileCertificate

theorem radialMatchedWeak_chain_exclusion (hRou : RectangleRouche) (ell : ℕ) (z : ProfileMatchingBall)
    (hz₁ : z.val.1=0) (hz : diskProfile (profileMatchingParameter z)=0)
    (hc : Continuous (radialMatchedFreeMassFunction z)) (R : ℝ)
    (hLR : radialShootingR (profileMatchingParameter z) < R)
    (w : SpectralHarmonicWeight R) (hw : w.density=radialMatchedFreeMassFunction z)
    (ζ : ℂ) (B B' : ℂ × ℂ →L[ℂ] ℂ × ℂ) (u₀ u₁ : SpectralHarmonicPair ell R)
    (hu₀ : u₀ ∈ spectralHarmonicCoreSubspace ell R (radialShootingR (profileMatchingParameter z)))
    (hu₁ : u₁ ∈ spectralHarmonicCoreSubspace ell R (radialShootingR (profileMatchingParameter z)))
    (hs : (ell=0 ∧ (ζ=0 ∨ ζ=1)) ∨ (ell=1 ∧ ζ=1/2))
    (hne : spectralHarmonicObservation ell R ((radialMatchedCore_radius_pos z).trans hLR) u₀ ≠ 0)
    (hdet : spectralValueDet
      (spectralPhysicalValueMap (spectralFreePositivePhysical ell (radialShootingB (profileMatchingParameter z)) ζ R))
      (spectralPhysicalValueMap (spectralFreeNegativePhysical ell (radialShootingB (profileMatchingParameter z)) ζ R)) ≠ 0)
    (hB : B = spectralFluxBoundary R (radialMatchedFreeMassFunction z R)
      (radialMatchedFreeTransportFunction z R)
      (spectralGaugeRobin (radialShootingFreeExterior z R) (deriv (radialShootingFreeExterior z) R) (spectralJetRobin
        (spectralFreePositivePhysical ell (radialShootingB (profileMatchingParameter z)) ζ R)
        (spectralFreeNegativePhysical ell (radialShootingB (profileMatchingParameter z)) ζ R))))
    (hB' : B' = spectralFluxBoundarySlope R (radialMatchedFreeMassFunction z R)
      (spectralGaugeRobinSlope (radialShootingFreeExterior z R) (deriv (fun lam => spectralJetRobin
        (spectralFreePositivePhysical ell (radialShootingB (profileMatchingParameter z)) lam R)
        (spectralFreeNegativePhysical ell (radialShootingB (profileMatchingParameter z)) lam R)) ζ)))
    (he₀ : let hR := (radialMatchedCore_radius_pos z).trans hLR
      ∀ v : spectralHarmonicCoreSubspace ell R (radialShootingR (profileMatchingParameter z)),
        spectralHarmonicPairComplexForm ell R w u₀ v =
          inner ℂ (radialMatchedLimitWeakOperator ell z hc R hR ζ B
            (spectralHarmonicObservation ell R hR u₀)) v)
    (he₁ : let hR := (radialMatchedCore_radius_pos z).trans hLR
      ∀ v : spectralHarmonicCoreSubspace ell R (radialShootingR (profileMatchingParameter z)),
        spectralHarmonicPairComplexForm ell R w u₁ v =
          inner ℂ (radialMatchedLimitWeakOperator ell z hc R hR ζ B
            (spectralHarmonicObservation ell R hR u₁) +
            spectralLowerOrderSlope ell R hR (spectralRadialWeightMultiplier R w) B'
              (spectralHarmonicObservation ell R hR u₀)) v) :
    False := by
  let L := radialShootingR (profileMatchingParameter z)
  have hL : 0 < L := radialMatchedCore_radius_pos z
  let hR := hL.trans hLR
  let β := radialShootingB (profileMatchingParameter z)
  let P := spectralFreePositivePhysical ell β ζ
  let N := spectralFreeNegativePhysical ell β ζ
  let M := spectralJetRobin (P R) (N R)
  let M' := deriv (fun lam => spectralJetRobin
    (spectralFreePositivePhysical ell β lam R) (spectralFreeNegativePhysical ell β lam R)) ζ
  have hζ : -(1/32 : ℝ) ≤ ζ.re := by
    rcases hs with ⟨_,rfl | rfl⟩ | ⟨_,rfl⟩ <;> norm_num
  obtain ⟨c,hcore,hrep⟩ := radialMatchedWeak_free_coefficients ell z hz₁ hz hc R hLR w hw
    ζ hζ u₀ hu₀ hdet B hB he₀
  have hcne : c ≠ 0 := by
    intro hzC
    obtain ⟨hf,_,C,hg,_⟩ := radialMatchedWeak_core ell z hc R hLR w hw ζ B u₀ hu₀ he₀
    apply hne
    apply spectralHarmonicObservation_zero_of_exterior_gauge ell L R hL hLR u₀
      (radialShootingFreeExterior z) (fun r hr => radialShootingFreeExterior_ne_zero z r hr.1.le)
      hf C hg
    intro r hr
    rw [hrep hr,hzC]
    simp only [Prod.fst_zero,Prod.snd_zero,zero_smul,add_zero]
  have hab : c.1 ≠ 0 ∨ c.2 ≠ 0 := by
    by_cases h : c.1=0
    · right
      intro hh
      exact hcne (Prod.ext h hh)
    · exact Or.inl h
  obtain ⟨X,hXc,_,hCX,hDX,hRX⟩ := radialMatchedWeak_chain_physical_extension ell z hz₁ hz hc R hLR
    w hw ζ B B' u₀ u₁ hu₀ hu₁ M M' hB hB' he₀ he₁
  let U₀ := fun r => c.1 • P r+c.2 • N r
  have hvR := radialMatchedWeak_coefficient_trace ell z R hLR ζ hζ u₀ c hrep
  apply radialFreePhysical_generalized_exclusion hRou (profileMatchingParameter z) hz ell ζ hs R hLR
    c.1 c.2 hab U₀ X (fun _ _ => rfl) _ hCX hXc _ hdet _
  · simpa only [U₀,spectralFreeCoreBoundary_linear] using hcore
  · intro r hr
    have h := hDX r hr
    rw [hrep hr] at h
    exact h
  · change spectralPhysicalDerivativeMap (X R) = M (spectralPhysicalValueMap (X R)) +
      M' (spectralPhysicalValueMap (U₀ R))
    rw [hvR]
    exact hRX

end DefocusingNLS

end OAI
