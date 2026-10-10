import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralFirstFluxPrimitive
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralLocalClassicalFlux

namespace OAI

/-! The exact weak equation gives a classical first channel throughout the exterior. -/

open Set MeasureTheory
open scoped SchwartzMap
namespace DefocusingNLS

theorem spectralFirst_classical (ell : ℕ) (R l : ℝ) (hR : 0 < R) (hl : 0 < l)
    (w a : SpectralHarmonicWeight R) (u : SpectralHarmonicPair ell R) (c ζ : ℂ)
    (B : ℂ × ℂ →L[ℂ] ℂ × ℂ)
    (hw : ContinuousOn w.density (Ioo 0 R)) (ha : ContinuousOn a.density (Ioo 0 R))
    (hpos : ∀ x ∈ Ioo 0 R, 0 < w.density x)
    (he : ∀ v : spectralHarmonicCoreSubspace ell R l,
      spectralHarmonicPairComplexForm ell R w u v=
      inner ℂ (spectralLowerOrderOperator ell R hR
        (spectralRadialWeightMultiplier R w) (spectralRadialWeightMultiplier R a) c ζ B
        (spectralHarmonicObservation ell R hR u)) v) :
    DifferentiableOn ℝ (spectralHarmonicRepresentative ell R hR u.fst) (Ioo l R) ∧
      ContinuousOn (deriv (spectralHarmonicRepresentative ell R hR u.fst)) (Ioo l R) ∧
      ∀ x ∈ Ioo l R,
        HasDerivAt (spectralSecondClassicalFlux ell R hR w (spectralNegWeight a) (spectralSwapPair ell R u))
          (spectralSecondContinuousSource ell R hR w (spectralSwapPair ell R u) (-c) (-ζ) x) x := by
  have hlocal (x : ℝ) (hx : x ∈ Ioo l R) :
      DifferentiableAt ℝ (spectralHarmonicRepresentative ell R hR u.fst) x ∧
      ContinuousAt (deriv (spectralHarmonicRepresentative ell R hR u.fst)) x ∧
      HasDerivAt (spectralSecondClassicalFlux ell R hR w (spectralNegWeight a) (spectralSwapPair ell R u))
        (spectralSecondContinuousSource ell R hR w (spectralSwapPair ell R u) (-c) (-ζ) x) x := by
    let α := (l+x)/2
    let β := (x+R)/2
    have hα : l < α := by dsimp only [α]; linarith [hx.1]
    have hαx : α < x := by dsimp only [α]; linarith [hx.1]
    have hxβ : x < β := by dsimp only [β]; linarith [hx.2]
    have hβ : β < R := by dsimp only [β]; linarith [hx.2]
    have hs : Ioo α β ⊆ Ioo 0 R := fun t ht => ⟨(hl.trans hα).trans ht.1,ht.2.trans hβ⟩
    obtain ⟨P,hP,hflux⟩ := spectralFirstFlux_primitive ell R l α β hR hl hα
      (hαx.trans hxβ) hβ w a u c ζ B hw ha he
    obtain ⟨hdf,hdc,hdF⟩ := spectralLocalFlux_classical ell R α β hR (hl.trans hα) hβ.le
      w (spectralNegWeight a) (spectralSwapPair ell R u) P
      (spectralSecondContinuousSource ell R hR w (spectralSwapPair ell R u) (-c) (-ζ))
      (hw.mono hs) (ha.neg.mono hs) (fun t ht => hpos t (hs ht)) hP hflux
    exact ⟨hdf x ⟨hαx,hxβ⟩,hdc.continuousAt (Ioo_mem_nhds hαx hxβ),hdF x ⟨hαx,hxβ⟩⟩
  exact ⟨fun x hx => (hlocal x hx).1.differentiableWithinAt,
    fun x hx => (hlocal x hx).2.1.continuousWithinAt,fun x hx => (hlocal x hx).2.2⟩

end DefocusingNLS

end OAI
