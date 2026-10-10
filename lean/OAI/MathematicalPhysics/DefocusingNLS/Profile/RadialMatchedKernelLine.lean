import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedWeakDeterminant
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralKernelCoefficientLine
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralGaugeObservationLine

namespace OAI

/-! The actual constrained limiting pencil has a one-dimensional kernel
whenever its kernel is nonzero. The proof uses its physical H coefficients
and unique harmonic continuation into the core. -/

open Set Filter
namespace DefocusingNLS
open ProfileCertificate
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem radialMatchedWeak_free_coefficients (ell : ℕ) (z : ProfileMatchingBall)
    (hz₁ : z.val.1 = 0) (hz : diskProfile (profileMatchingParameter z) = 0)
    (hc : Continuous (radialMatchedFreeMassFunction z)) (R : ℝ)
    (hLR : radialShootingR (profileMatchingParameter z) < R)
    (w : SpectralHarmonicWeight R) (hw : w.density = radialMatchedFreeMassFunction z)
    (ζ : ℂ) (hζ : -(1/32 : ℝ) ≤ ζ.re) (u : SpectralHarmonicPair ell R)
    (hu : u ∈ spectralHarmonicCoreSubspace ell R (radialShootingR (profileMatchingParameter z)))
    (hdet : spectralValueDet
      (spectralPhysicalValueMap (spectralFreePositivePhysical ell (radialShootingB (profileMatchingParameter z)) ζ R))
      (spectralPhysicalValueMap (spectralFreeNegativePhysical ell (radialShootingB (profileMatchingParameter z)) ζ R)) ≠ 0)
    (B : ℂ × ℂ →L[ℂ] ℂ × ℂ)
    (hBoundary : B = spectralFluxBoundary R (radialMatchedFreeMassFunction z R)
      (radialMatchedFreeTransportFunction z R)
      (spectralGaugeRobin (radialShootingFreeExterior z R) (deriv (radialShootingFreeExterior z) R)
        (spectralJetRobin
          (spectralFreePositivePhysical ell (radialShootingB (profileMatchingParameter z)) ζ R)
          (spectralFreeNegativePhysical ell (radialShootingB (profileMatchingParameter z)) ζ R))))
    (he : let hR := (radialMatchedCore_radius_pos z).trans hLR
      ∀ v : spectralHarmonicCoreSubspace ell R (radialShootingR (profileMatchingParameter z)),
        spectralHarmonicPairComplexForm ell R w u v =
          inner ℂ (radialMatchedLimitWeakOperator ell z hc R hR ζ B
            (spectralHarmonicObservation ell R hR u)) v) :
    let L := radialShootingR (profileMatchingParameter z)
    let hR := (radialMatchedCore_radius_pos z).trans hLR
    let P := spectralFreePositivePhysical ell (radialShootingB (profileMatchingParameter z)) ζ
    let N := spectralFreeNegativePhysical ell (radialShootingB (profileMatchingParameter z)) ζ
    ∃ c : ℂ × ℂ,
      c.1 • spectralFreeCoreBoundary ell L (P L) +
        c.2 • spectralFreeCoreBoundary ell L (N L) = 0 ∧
      EqOn (spectralPhysicalGaugePair (radialShootingFreeExterior z)
        (spectralHarmonicRepresentative ell R hR u.fst)
        (spectralHarmonicRepresentative ell R hR u.snd))
        (fun r => c.1 • P r + c.2 • N r) (Ioo L R) := by
  let L := radialShootingR (profileMatchingParameter z)
  have hL : 0 < L := radialMatchedCore_radius_pos z
  obtain ⟨c, hrep⟩ := radialMatchedWeak_free_representation_of_boundary ell z hz₁ hz hc R hLR
    w hw ζ hζ u hdet B hBoundary he
  refine ⟨c, ?_, hrep⟩
  have hY : ContinuousOn (fun r =>
      c.1 • spectralFreePositivePhysical ell (radialShootingB (profileMatchingParameter z)) ζ r +
      c.2 • spectralFreeNegativePhysical ell (radialShootingB (profileMatchingParameter z)) ζ r)
      (Ico L R) := by
    intro r hr
    exact (spectralFreeCombination_hasDerivAt _ ζ _ _ _ c.1 c.2 r
      (spectralFreePositivePhysical_hasDerivAt ell _ ζ hζ r (hL.trans_le hr.1))
      (spectralFreeNegativePhysical_hasDerivAt ell _ ζ hζ r (hL.trans_le hr.1))).continuousAt.continuousWithinAt
  have hb := radialMatchedWeak_physical_core ell z hz₁ hz hc R hLR w hw ζ B u hu he _ hY hrep.symm
  simpa only [spectralFreeCoreBoundary_linear] using hb

theorem radialMatchedWeak_observation_line (ell : ℕ) (z : ProfileMatchingBall)
    (hz₁ : z.val.1 = 0) (hz : diskProfile (profileMatchingParameter z) = 0)
    (hc : Continuous (radialMatchedFreeMassFunction z)) (R : ℝ)
    (hLR : radialShootingR (profileMatchingParameter z) < R)
    (w : SpectralHarmonicWeight R) (hw : w.density = radialMatchedFreeMassFunction z)
    (ζ : ℂ) (hζ : -(1/32 : ℝ) ≤ ζ.re) (u v : SpectralHarmonicPair ell R)
    (hu : u ∈ spectralHarmonicCoreSubspace ell R (radialShootingR (profileMatchingParameter z)))
    (hv : v ∈ spectralHarmonicCoreSubspace ell R (radialShootingR (profileMatchingParameter z)))
    (hne : spectralHarmonicObservation ell R ((radialMatchedCore_radius_pos z).trans hLR) u ≠ 0)
    (hdet : spectralValueDet
      (spectralPhysicalValueMap (spectralFreePositivePhysical ell (radialShootingB (profileMatchingParameter z)) ζ R))
      (spectralPhysicalValueMap (spectralFreeNegativePhysical ell (radialShootingB (profileMatchingParameter z)) ζ R)) ≠ 0)
    (B : ℂ × ℂ →L[ℂ] ℂ × ℂ)
    (hBoundary : B = spectralFluxBoundary R (radialMatchedFreeMassFunction z R)
      (radialMatchedFreeTransportFunction z R)
      (spectralGaugeRobin (radialShootingFreeExterior z R) (deriv (radialShootingFreeExterior z) R)
        (spectralJetRobin
          (spectralFreePositivePhysical ell (radialShootingB (profileMatchingParameter z)) ζ R)
          (spectralFreeNegativePhysical ell (radialShootingB (profileMatchingParameter z)) ζ R))))
    (heu : let hR := (radialMatchedCore_radius_pos z).trans hLR
      ∀ t : spectralHarmonicCoreSubspace ell R (radialShootingR (profileMatchingParameter z)),
        spectralHarmonicPairComplexForm ell R w u t =
          inner ℂ (radialMatchedLimitWeakOperator ell z hc R hR ζ B
            (spectralHarmonicObservation ell R hR u)) t)
    (hev : let hR := (radialMatchedCore_radius_pos z).trans hLR
      ∀ t : spectralHarmonicCoreSubspace ell R (radialShootingR (profileMatchingParameter z)),
        spectralHarmonicPairComplexForm ell R w v t =
          inner ℂ (radialMatchedLimitWeakOperator ell z hc R hR ζ B
            (spectralHarmonicObservation ell R hR v)) t) :
    ∃ a : ℂ, spectralHarmonicObservation ell R ((radialMatchedCore_radius_pos z).trans hLR) v =
      a • spectralHarmonicObservation ell R ((radialMatchedCore_radius_pos z).trans hLR) u := by
  let L := radialShootingR (profileMatchingParameter z)
  have hL : 0 < L := radialMatchedCore_radius_pos z
  let P := spectralFreePositivePhysical ell (radialShootingB (profileMatchingParameter z)) ζ
  let N := spectralFreeNegativePhysical ell (radialShootingB (profileMatchingParameter z)) ζ
  obtain ⟨cu, hcu, hru⟩ := radialMatchedWeak_free_coefficients ell z hz₁ hz hc R hLR
    w hw ζ hζ u hu hdet B hBoundary heu
  obtain ⟨cv, hcv, hrv⟩ := radialMatchedWeak_free_coefficients ell z hz₁ hz hc R hLR
    w hw ζ hζ v hv hdet B hBoundary hev
  obtain ⟨hfu, _, Cu, hgu, _⟩ := radialMatchedWeak_core ell z hc R hLR w hw ζ B u hu heu
  obtain ⟨hfv, _, Cv, hgv, _⟩ := radialMatchedWeak_core ell z hc R hLR w hw ζ B v hv hev
  have hcune : cu ≠ 0 := by
    intro hzcu
    apply hne
    apply spectralHarmonicObservation_zero_of_exterior_gauge ell L R hL hLR u
      (radialShootingFreeExterior z) (fun r hr => radialShootingFreeExterior_ne_zero z r hr.1.le)
      hfu Cu hgu
    intro r hr
    rw [hru hr, hzcu]
    simp only [Prod.fst_zero, Prod.snd_zero, zero_smul, add_zero]
  have hD : matchingColumnDeterminant (spectralFreeCoreBoundary ell L (P L))
      (spectralFreeCoreBoundary ell L (N L)) = 0 := by
    by_contra hD
    obtain ⟨h1,h2⟩ := matchingColumn_coefficients_zero _ _ cu.1 cu.2 hD hcu
    exact hcune (Prod.ext h1 h2)
  obtain ⟨a, ha⟩ := matchingColumn_kernel_line _ _
    (spectralFreePositivePhysical_core_ne_zero ell _ L ζ hL hζ) hD cu cv hcune hcu hcv
  refine ⟨a, ?_⟩
  apply spectralHarmonicObservation_eq_of_gauge_values ell L R hL hLR v u
    (radialShootingFreeExterior z) (fun r hr => radialShootingFreeExterior_ne_zero z r hr.1.le)
    a Cv Cu hfv hfu hgv hgu
  intro r hr
  have heq : spectralPhysicalGaugePair (radialShootingFreeExterior z)
      (spectralHarmonicRepresentative ell R (hL.trans hLR) v.fst)
      (spectralHarmonicRepresentative ell R (hL.trans hLR) v.snd) r =
      a • spectralPhysicalGaugePair (radialShootingFreeExterior z)
        (spectralHarmonicRepresentative ell R (hL.trans hLR) u.fst)
        (spectralHarmonicRepresentative ell R (hL.trans hLR) u.snd) r := by
    rw [hrv hr, hru hr, ha]
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, mul_smul, smul_add]
  exact ⟨congrArg (fun X : E₄ => X.1.1) heq, congrArg (fun X : E₄ => X.2.1) heq⟩

end DefocusingNLS

end OAI
