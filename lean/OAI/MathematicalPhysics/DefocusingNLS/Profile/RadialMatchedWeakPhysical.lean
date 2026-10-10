import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPhysicalGaugeTransfer
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedWeakRobinC1
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedWeakExterior

namespace OAI

/-! The actual weak limiting equation gives a classical physical solution with its outer Robin trace. -/

open Set Filter
namespace DefocusingNLS
open ProfileCertificate

theorem radialMatchedWeak_physical_extension_of_boundary (ell : ℕ) (z : ProfileMatchingBall)
    (hz₁ : z.val.1=0) (hz : diskProfile (profileMatchingParameter z)=0)
    (hc : Continuous (radialMatchedFreeMassFunction z)) (R : ℝ)
    (hLR : radialShootingR (profileMatchingParameter z) < R)
    (δ : ℝ) (hlδ : radialShootingR (profileMatchingParameter z) < δ) (hδR : δ < R)
    (w : SpectralHarmonicWeight R) (hw : w.density=radialMatchedFreeMassFunction z)
    (ζ : ℂ) (M B : ℂ × ℂ →L[ℂ] ℂ × ℂ)
    (hBoundary : B=spectralFluxBoundary R (radialMatchedFreeMassFunction z R)
      (radialMatchedFreeTransportFunction z R)
      (spectralGaugeRobin (radialShootingFreeExterior z R) (deriv (radialShootingFreeExterior z) R) M))
    (u : SpectralHarmonicPair ell R)
    (he : let hR := (radialMatchedCore_radius_pos z).trans hLR
      ∀ v : spectralHarmonicCoreSubspace ell R (radialShootingR (profileMatchingParameter z)),
        spectralHarmonicPairComplexForm ell R w u v=
          inner ℂ (radialMatchedLimitWeakOperator ell z hc R hR ζ B
            (spectralHarmonicObservation ell R hR u)) v) :
    let hR := (radialMatchedCore_radius_pos z).trans hLR
    let Q := radialShootingFreeExterior z
    ∃ f g : ℝ → ℂ, Continuous f ∧ Continuous g ∧
      ContinuousOn (deriv f) (Icc δ R) ∧ ContinuousOn (deriv g) (Icc δ R) ∧
      EqOn f (spectralHarmonicRepresentative ell R hR u.fst) (Icc δ R) ∧
      EqOn g (spectralHarmonicRepresentative ell R hR u.snd) (Icc δ R) ∧
      ContinuousOn (spectralPhysicalGaugePair Q f g) (Icc δ R) ∧
      (∀ r ∈ Ioo δ R, HasDerivAt (spectralPhysicalGaugePair Q f g)
        (spectralFreePhysicalPairField (radialShootingB (profileMatchingParameter z)) ζ
          ((ell : ℂ)*((ell : ℂ)+10)) r (spectralPhysicalGaugePair Q f g r)) r) ∧
      spectralPhysicalDerivativeMap (spectralPhysicalGaugePair Q f g R)=
        M (spectralPhysicalValueMap (spectralPhysicalGaugePair Q f g R)) := by
  dsimp only at he ⊢
  let hR := (radialMatchedCore_radius_pos z).trans hLR
  let Q := radialShootingFreeExterior z
  obtain ⟨f,g,hf,hg,hdf,hdg,hef,heg,hRobin⟩ := radialMatchedWeak_robin_C1 ell z hc R hLR
    δ hlδ hδR w hw ζ (spectralGaugeRobin (Q R) (deriv Q R) M) B hBoundary u he
  have hQc : ContinuousOn Q (Icc δ R) :=
    (radialShootingFreeExterior_contDiffOn z).continuousOn.mono
      (fun r hr => ((radialMatchedCore_radius_pos z).trans hlδ).trans_le hr.1)
  have hDQ : ContinuousOn (deriv Q) (Icc δ R) := fun r hr =>
    (radialShootingFreeExterior_hasDerivAt_deriv z r
      (((radialMatchedCore_radius_pos z).trans hlδ).trans_le hr.1)).continuousAt.continuousWithinAt
  have hD := radialMatchedWeak_physical_hasDerivAt ell z hz₁ hz hc R hLR w hw ζ B u he
  refine ⟨f,g,hf,hg,hdf,hdg,hef,heg,
    spectralPhysicalGaugePair_continuousOn Q f g _ hQc hDQ hf.continuousOn hdf hg.continuousOn hdg,
    ?_,?_⟩
  · intro r hr
    exact spectralPhysicalGaugePair_hasDerivAt_of_eqOn Q f g _ _ (Ioo δ R) isOpen_Ioo
      (fun t ht => hef ⟨ht.1.le,ht.2.le⟩) (fun t ht => heg ⟨ht.1.le,ht.2.le⟩) r hr
      (spectralFreePhysicalPairField (radialShootingB (profileMatchingParameter z)) ζ
        ((ell : ℂ)*((ell : ℂ)+10)) r) (hD r ⟨hlδ.trans hr.1,hr.2⟩)
  · apply spectralPhysicalGaugePair_robin
    exact (spectralGaugeRobin_condition (Q R) (deriv Q R)
      (radialShootingFreeExterior_ne_zero z R hLR.le) M (f R,g R) (deriv f R,deriv g R)).mpr hRobin

theorem radialMatchedWeak_physical_extension (ell : ℕ) (z : ProfileMatchingBall)
    (hz₁ : z.val.1=0) (hz : diskProfile (profileMatchingParameter z)=0)
    (hc : Continuous (radialMatchedFreeMassFunction z)) (R : ℝ)
    (hLR : radialShootingR (profileMatchingParameter z) < R)
    (δ : ℝ) (hlδ : radialShootingR (profileMatchingParameter z) < δ) (hδR : δ < R)
    (w : SpectralHarmonicWeight R) (hw : w.density=radialMatchedFreeMassFunction z)
    (ζ : ℂ) (M : ℂ × ℂ →L[ℂ] ℂ × ℂ) (u : SpectralHarmonicPair ell R)
    (he : let hR := (radialMatchedCore_radius_pos z).trans hLR
      let Q := radialShootingFreeExterior z
      let B := spectralFluxBoundary R (radialMatchedFreeMassFunction z R)
        (radialMatchedFreeTransportFunction z R) (spectralGaugeRobin (Q R) (deriv Q R) M)
      ∀ v : spectralHarmonicCoreSubspace ell R (radialShootingR (profileMatchingParameter z)),
        spectralHarmonicPairComplexForm ell R w u v=
          inner ℂ (radialMatchedLimitWeakOperator ell z hc R hR ζ B
            (spectralHarmonicObservation ell R hR u)) v) :
    let hR := (radialMatchedCore_radius_pos z).trans hLR
    let Q := radialShootingFreeExterior z
    ∃ f g : ℝ → ℂ, Continuous f ∧ Continuous g ∧
      ContinuousOn (deriv f) (Icc δ R) ∧ ContinuousOn (deriv g) (Icc δ R) ∧
      EqOn f (spectralHarmonicRepresentative ell R hR u.fst) (Icc δ R) ∧
      EqOn g (spectralHarmonicRepresentative ell R hR u.snd) (Icc δ R) ∧
      ContinuousOn (spectralPhysicalGaugePair Q f g) (Icc δ R) ∧
      (∀ r ∈ Ioo δ R, HasDerivAt (spectralPhysicalGaugePair Q f g)
        (spectralFreePhysicalPairField (radialShootingB (profileMatchingParameter z)) ζ
          ((ell : ℂ)*((ell : ℂ)+10)) r (spectralPhysicalGaugePair Q f g r)) r) ∧
      spectralPhysicalDerivativeMap (spectralPhysicalGaugePair Q f g R)=
        M (spectralPhysicalValueMap (spectralPhysicalGaugePair Q f g R)) := by
  exact radialMatchedWeak_physical_extension_of_boundary ell z hz₁ hz hc R hLR δ hlδ hδR
    w hw ζ M (spectralFluxBoundary R (radialMatchedFreeMassFunction z R)
      (radialMatchedFreeTransportFunction z R)
      (spectralGaugeRobin (radialShootingFreeExterior z R) (deriv (radialShootingFreeExterior z) R) M))
    rfl u he

end DefocusingNLS

end OAI
