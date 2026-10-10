import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedKernelLine

namespace OAI

/-! The outgoing representation determines the physical value trace at the
outer endpoint, where the weak derivative need not be used. -/

open Set
namespace DefocusingNLS
open ProfileCertificate

theorem radialMatchedWeak_coefficient_trace (ell : ℕ) (z : ProfileMatchingBall)
    (R : ℝ) (hLR : radialShootingR (profileMatchingParameter z) < R)
    (ζ : ℂ) (hζ : -(1/32 : ℝ) ≤ ζ.re) (u : SpectralHarmonicPair ell R) (c : ℂ × ℂ)
    (he : let L := radialShootingR (profileMatchingParameter z)
      let hR := (radialMatchedCore_radius_pos z).trans hLR
      EqOn (spectralPhysicalGaugePair (radialShootingFreeExterior z)
        (spectralHarmonicRepresentative ell R hR u.fst) (spectralHarmonicRepresentative ell R hR u.snd))
        (fun r => c.1 • spectralFreePositivePhysical ell (radialShootingB (profileMatchingParameter z)) ζ r +
          c.2 • spectralFreeNegativePhysical ell (radialShootingB (profileMatchingParameter z)) ζ r) (Ioo L R)) :
    spectralPhysicalValueMap
      (c.1 • spectralFreePositivePhysical ell (radialShootingB (profileMatchingParameter z)) ζ R +
        c.2 • spectralFreeNegativePhysical ell (radialShootingB (profileMatchingParameter z)) ζ R) =
      spectralGaugeColumns (radialShootingFreeExterior z R)
        (spectralHarmonicPairTraces ell R ((radialMatchedCore_radius_pos z).trans hLR) u) := by
  let L := radialShootingR (profileMatchingParameter z)
  have hL : 0 < L := radialMatchedCore_radius_pos z
  let hR := hL.trans hLR
  let Q := radialShootingFreeExterior z
  let f := spectralHarmonicRepresentative ell R hR u.fst
  let g := spectralHarmonicRepresentative ell R hR u.snd
  let V := fun r => c.1 • spectralFreePositivePhysical ell (radialShootingB (profileMatchingParameter z)) ζ r +
    c.2 • spectralFreeNegativePhysical ell (radialShootingB (profileMatchingParameter z)) ζ r
  have hVc : ContinuousOn V (Icc L R) := fun r hr =>
    (spectralFreeCombination_hasDerivAt _ ζ _ _ _ c.1 c.2 r
      (spectralFreePositivePhysical_hasDerivAt ell _ ζ hζ r (hL.trans_le hr.1))
      (spectralFreeNegativePhysical_hasDerivAt ell _ ζ hζ r (hL.trans_le hr.1))).continuousAt.continuousWithinAt
  have hQc : ContinuousOn Q (Icc L R) := fun r hr =>
    (radialShootingFreeExterior_hasDerivAt z r (hL.trans_le hr.1)).continuousAt.continuousWithinAt
  have hfc : ContinuousOn f (Icc L R) := spectralHarmonicRepresentative_continuousOn_closed ell R L hR hL u.fst
  have hgc : ContinuousOn g (Icc L R) := spectralHarmonicRepresentative_continuousOn_closed ell R L hR hL u.snd
  have hright : ContinuousOn (fun r => spectralGaugeColumns (Q r) (f r,g r)) (Icc L R) := by
    simp only [spectralGaugeColumns,spectralTwoColumns_apply]
    fun_prop
  have hv : EqOn (fun r => spectralPhysicalValueMap (V r))
      (fun r => spectralGaugeColumns (Q r) (f r,g r)) (Ioo L R) := by
    intro r hr
    change spectralPhysicalValueMap (V r) = spectralGaugeColumns (Q r) (f r,g r)
    have hh : spectralPhysicalGaugePair Q f g r = V r := he hr
    rw [← hh,spectralPhysicalGaugePair_value]
  have hclosed : Icc L R ⊆ closure (Ioo L R) := by rw [closure_Ioo hLR.ne]
  have heR := hv.of_subset_closure
    (spectralPhysicalValueMap.continuous.comp_continuousOn hVc) hright Ioo_subset_Icc_self hclosed
      (show R ∈ Icc L R from ⟨hLR.le,le_rfl⟩)
  change spectralPhysicalValueMap (V R) = spectralGaugeColumns (Q R) (f R,g R) at heR
  have ht : (f R,g R)=spectralHarmonicPairTraces ell R hR u := spectralHarmonicRepresentative_trace ell R hR u
  rw [ht] at heR
  exact heR

end DefocusingNLS

end OAI
