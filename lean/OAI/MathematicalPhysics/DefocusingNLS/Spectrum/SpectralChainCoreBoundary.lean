import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralChainClosedBoundary
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralForcedEdgeBoundary

namespace OAI

/-! The first forced flux extends continuously to the core interface. -/

open Set MeasureTheory
open scoped SchwartzMap
namespace DefocusingNLS

theorem spectralFirstChain_closedBoundary_at_core (ell : ℕ) (L R : ℝ) (hR : 0 < R)
    (hL : 0 < L) (hLR : L < R)
    (w a : SpectralHarmonicWeight R) (u₀ u₁ : SpectralHarmonicPair ell R) (c ζ : ℂ)
    (B B' : ℂ × ℂ →L[ℂ] ℂ × ℂ)
    (hw : ContinuousOn w.density (Ioo 0 R)) (ha : ContinuousOn a.density (Ioo 0 R))
    (hwc : ContinuousOn w.density (Icc L R))
    (hpos : ∀ x ∈ Ioo 0 R, 0 < w.density x)
    (he : ∀ v : spectralHarmonicCoreSubspace ell R L,
      spectralHarmonicPairComplexForm ell R w u₁ v =
      inner ℂ (spectralLowerOrderOperator ell R hR
        (spectralRadialWeightMultiplier R w) (spectralRadialWeightMultiplier R a) c ζ B
        (spectralHarmonicObservation ell R hR u₁) +
        spectralLowerOrderSlope ell R hR (spectralRadialWeightMultiplier R w) B'
          (spectralHarmonicObservation ell R hR u₀)) v) :
    ∃ P : ℝ → ℂ, Continuous P ∧
      (∀ x ∈ Icc L R, HasDerivAt P (spectralFirstChainSource ell R hR w u₀ u₁ c ζ x) x) ∧
      EqOn (spectralSecondClassicalFlux ell R hR w (spectralNegWeight a) (spectralSwapPair ell R u₁))
        P (Ioo L R) ∧
      (∀ᵐ x, x ∈ Icc L R →
        spectralSecondFlux ell R w (spectralNegWeight a) (spectralSwapPair ell R u₁) x = P x) ∧
      P R = (B (spectralHarmonicPairTraces ell R hR u₁)).1 +
        (B' (spectralHarmonicPairTraces ell R hR u₀)).1 := by
  have hs : Ioo L R ⊆ Ioo 0 R := fun x hx => ⟨hL.trans hx.1,hx.2⟩
  have hGc : ContinuousOn (spectralFirstChainSource ell R hR w u₀ u₁ c ζ) (Icc L R) :=
    (spectralSecondContinuousSource_closed ell R L hR hL w
      (spectralSwapPair ell R u₁) (-c) (-ζ) hwc).add
      ((Complex.continuous_ofReal.continuousOn.pow 11).mul
        (hwc.smul (spectralHarmonicRepresentative_continuousOn_closed ell R L hR hL u₀.snd)))
  apply spectralForced_closedBoundary_at_edge ell L R hL.le hR hLR
    w (spectralNegWeight a) (spectralSwapPair ell R u₁) _ _
    (hw.mono hs) (ha.neg.mono hs) (fun x hx => hpos x (hs hx))
    ((spectralFirstChainSource_continuousOn ell R hR w u₀ u₁ c ζ hw).mono hs) hGc
    ((spectralSecondFlux_locallyIntegrableOn ell R w (spectralNegWeight a)
      (spectralSwapPair ell R u₁) hw ha.neg).mono_set hs)
    (spectralFirstChain_weak_flux ell L R hL.le hR w a u₀ u₁ c ζ B B' hw he)
  intro f hfR hf
  have ht := he ⟨spectralFirstTest ell R f,spectralFirstTest_core ell R L f
    (fun x hx => hf x hx)⟩
  simpa only [hfR,star_one,one_mul] using
    spectralFirstChain_boundary_flux ell R hR w a u₀ u₁ c ζ B B' f ht

end DefocusingNLS

end OAI
