import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedWeakForcedEquation
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedWeakChainCoreLimit
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralChainCoreC1
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralGaugeRobinDerivative
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPhysicalGaugeTransfer

namespace OAI

/-! A weak free first chain gives the actual physical forced boundary problem. -/

open Set Filter
namespace DefocusingNLS
open ProfileCertificate

theorem radialMatchedWeak_chain_physical_extension (ell : ℕ) (z : ProfileMatchingBall)
    (hz₁ : z.val.1=0) (hz : diskProfile (profileMatchingParameter z)=0)
    (hc : Continuous (radialMatchedFreeMassFunction z)) (R : ℝ)
    (hLR : radialShootingR (profileMatchingParameter z) < R)
    (w : SpectralHarmonicWeight R) (hw : w.density=radialMatchedFreeMassFunction z)
    (ζ : ℂ) (B B' : ℂ × ℂ →L[ℂ] ℂ × ℂ) (u₀ u₁ : SpectralHarmonicPair ell R)
    (hu₀ : u₀ ∈ spectralHarmonicCoreSubspace ell R (radialShootingR (profileMatchingParameter z)))
    (hu₁ : u₁ ∈ spectralHarmonicCoreSubspace ell R (radialShootingR (profileMatchingParameter z)))
    (M M' : ℂ × ℂ →L[ℂ] ℂ × ℂ)
    (hB : B = spectralFluxBoundary R (radialMatchedFreeMassFunction z R)
      (radialMatchedFreeTransportFunction z R)
      (spectralGaugeRobin (radialShootingFreeExterior z R) (deriv (radialShootingFreeExterior z) R) M))
    (hB' : B' = spectralFluxBoundarySlope R (radialMatchedFreeMassFunction z R)
      (spectralGaugeRobinSlope (radialShootingFreeExterior z R) M'))
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
    let L := radialShootingR (profileMatchingParameter z)
    let hR := (radialMatchedCore_radius_pos z).trans hLR
    let Q := radialShootingFreeExterior z
    let X₀ := spectralPhysicalGaugePair Q (spectralHarmonicRepresentative ell R hR u₀.fst)
      (spectralHarmonicRepresentative ell R hR u₀.snd)
    ∃ X : ℝ → ((ℂ × ℂ) × (ℂ × ℂ)), ContinuousOn X (Icc L R) ∧
      EqOn X (spectralPhysicalGaugePair Q (spectralHarmonicRepresentative ell R hR u₁.fst)
        (spectralHarmonicRepresentative ell R hR u₁.snd)) (Ioo L R) ∧
      spectralFreeCoreBoundary ell L (X L)=0 ∧
      (∀ r ∈ Ioo L R, HasDerivAt X
        (spectralFreePhysicalPairField (radialShootingB (profileMatchingParameter z)) ζ
          ((ell : ℂ)*((ell : ℂ)+10)) r (X r)+spectralFreeChainSource (X₀ r)) r) ∧
      spectralPhysicalDerivativeMap (X R) = M (spectralPhysicalValueMap (X R)) +
        M' (spectralGaugeColumns (Q R) (spectralHarmonicPairTraces ell R hR u₀)) := by
  dsimp only at he₀ he₁ ⊢
  let L := radialShootingR (profileMatchingParameter z)
  have hL : 0 < L := radialMatchedCore_radius_pos z
  let hR := hL.trans hLR
  let Q := radialShootingFreeExterior z
  let a := spectralContinuousCoefficient R (radialMatchedFreeTransportFunction z)
    (continuous_const.mul (continuous_id.mul (continuous_radialAverage _ hc)))
  have hwc : Continuous w.density := by rw [hw]; exact hc
  have hac : Continuous a.density :=
    continuous_const.mul (continuous_id.mul (continuous_radialAverage _ hc))
  have hp (r : ℝ) (hr : 0 ≤ r) : 0 < w.density r := by
    rw [hw]
    exact radialMatchedFreeMass_pos z r hr
  let F : SpectralHarmonicPair ell R := spectralLowerOrderSlope ell R hR
    (spectralRadialWeightMultiplier R w) B' (spectralHarmonicObservation ell R hR u₀)
  have heF : ∀ v : spectralHarmonicCoreSubspace ell R L,
      spectralHarmonicPairComplexForm ell R w u₁ v =
        inner ℂ (radialMatchedLimitWeakOperator ell z hc R hR ζ B
          (spectralHarmonicObservation ell R hR u₁)+F) v := by
    simpa only [F,L,hR] using he₁
  have he₁' := radialMatchedWeak_forced_equation ell z hc R L hR w a hw rfl F ζ B u₁ heF
  have hb : B = spectralFluxBoundary R (w.density R) (a.density R)
      (spectralGaugeRobin (Q R) (deriv Q R) M) := by rw [hw]; exact hB
  have hb' : B' = spectralFluxBoundarySlope R (w.density R)
      (spectralGaugeRobinSlope (Q R) M') := by rw [hw]; exact hB'
  dsimp only [F] at he₁'
  rw [hb,hb'] at he₁'
  obtain ⟨f,g,hf,hg,hdf,hdg,hef,heg,_,hRobin⟩ := spectralWeakChain_robin_C1_at_core
    ell R L hR hL hLR w a u₀ u₁ 6 ζ (spectralGaugeRobin (Q R) (deriv Q R) M)
      (spectralGaugeRobinSlope (Q R) M') hwc.continuousOn hac.continuousOn
      hwc.continuousOn hac.continuousOn (fun r hr => hp r hr.1.le)
      (fun r hr => hp r (hL.le.trans hr.1)) he₁'
  let X := spectralPhysicalGaugePair Q f g
  have hQc : ContinuousOn Q (Icc L R) := fun r hr =>
    (radialShootingFreeExterior_hasDerivAt z r (hL.trans_le hr.1)).continuousAt.continuousWithinAt
  have hDQ : ContinuousOn (deriv Q) (Icc L R) := fun r hr =>
    (radialShootingFreeExterior_hasDerivAt_deriv z r (hL.trans_le hr.1)).continuousAt.continuousWithinAt
  have hXc : ContinuousOn X (Icc L R) :=
    spectralPhysicalGaugePair_continuousOn Q f g _ hQc hDQ hf.continuousOn hdf hg.continuousOn hdg
  have hXe : EqOn X (spectralPhysicalGaugePair Q
      (spectralHarmonicRepresentative ell R hR u₁.fst)
      (spectralHarmonicRepresentative ell R hR u₁.snd)) (Ioo L R) := by
    intro r hr
    apply spectralPhysicalGaugePair_congr
    · filter_upwards [isOpen_Ioo.mem_nhds hr] with t ht
      exact hef (Ioo_subset_Icc_self ht)
    · filter_upwards [isOpen_Ioo.mem_nhds hr] with t ht
      exact heg (Ioo_subset_Icc_self ht)
  refine ⟨X,hXc,hXe,?_,?_,?_⟩
  · exact radialMatchedWeak_chain_physical_core ell z hz₁ hz hc R hLR w hw ζ B B' u₀ u₁
      hu₀ hu₁ he₁ X (hXc.mono Ico_subset_Icc_self) hXe
  · intro r hr
    apply spectralPhysicalGaugePair_hasDerivAt_of_eqOn Q f g _ _ (Ioo L R) isOpen_Ioo
      (fun t ht => hef (Ioo_subset_Icc_self ht)) (fun t ht => heg (Ioo_subset_Icc_self ht)) r hr
      (fun Y => spectralFreePhysicalPairField (radialShootingB (profileMatchingParameter z)) ζ
        ((ell : ℂ)*((ell : ℂ)+10)) r Y + spectralFreeChainSource
          (spectralPhysicalGaugePair Q (spectralHarmonicRepresentative ell R hR u₀.fst)
            (spectralHarmonicRepresentative ell R hR u₀.snd) r))
    exact radialMatchedWeak_chain_physical_hasDerivAt ell z hz₁ hz hc R hLR w hw ζ B B' u₀ u₁ he₀ he₁ r hr
  · exact spectralPhysicalGaugePair_chain_robin Q f g R M M' _
      (radialShootingFreeExterior_ne_zero z R hLR.le) hRobin

end DefocusingNLS

end OAI
