import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralSecondClassicalFlux

namespace OAI

/-! Recovering a classical radial flux from its inhomogeneous weak equation.
This applies directly to the derivative load of a pencil chain. -/

open Set MeasureTheory
open scoped ContDiff
namespace DefocusingNLS

theorem spectralSecond_forced_classical (ell : ℕ) (R : ℝ) (hR : 0 < R)
    (w a : SpectralHarmonicWeight R) (u : SpectralHarmonicPair ell R) (G : ℝ → ℂ)
    (hw : ContinuousOn w.density (Ioo 0 R)) (ha : ContinuousOn a.density (Ioo 0 R))
    (hpos : ∀ x ∈ Ioo 0 R, 0 < w.density x) (hG : ContinuousOn G (Ioo 0 R))
    (he : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo 0 R →
        (∫ x, deriv φ x • spectralSecondFlux ell R w a u x) = -(∫ x, φ x • G x)) :
    DifferentiableOn ℝ (spectralHarmonicRepresentative ell R hR u.snd) (Ioo 0 R) ∧
      ContinuousOn (deriv (spectralHarmonicRepresentative ell R hR u.snd)) (Ioo 0 R) ∧
      ∀ x ∈ Ioo 0 R, HasDerivAt (spectralSecondClassicalFlux ell R hR w a u) (G x) x := by
  have hlocal (x : ℝ) (hx : x ∈ Ioo 0 R) :
      DifferentiableAt ℝ (spectralHarmonicRepresentative ell R hR u.snd) x ∧
      ContinuousAt (deriv (spectralHarmonicRepresentative ell R hR u.snd)) x ∧
      HasDerivAt (spectralSecondClassicalFlux ell R hR w a u)
        (G x) x := by
    let l := x/2
    let r := (x+R)/2
    have hl : 0 < l := by dsimp only [l]; linarith [hx.1]
    have hxl : l < x := by dsimp only [l]; linarith [hx.1]
    have hxr : x < r := by dsimp only [r]; linarith [hx.2]
    have hr : r < R := by dsimp only [r]; linarith [hx.2]
    have hs : Ioo l r ⊆ Ioo 0 R := fun t ht => ⟨hl.trans ht.1,ht.2.trans hr⟩
    obtain ⟨P,hP,hflux⟩ := spectralLocalFlux_primitive R l r hl (hxl.trans hxr) hr
      (spectralSecondFlux ell R w a u) G
      (spectralSecondFlux_locallyIntegrableOn ell R w a u hw ha) hG he
    have hPc : ContinuousOn P (Ioo l r) := fun t ht => (hP t ht).continuousAt.continuousWithinAt
    have hd (t : ℝ) (ht : t ∈ Ioo l r) := spectralSecondFlux_hasDerivAt ell R l r hR
      hl hr.le w a u P (hw.mono hs) (ha.mono hs) (fun s hs' => hpos s (hs hs')) hPc hflux t ht
    have heq (t : ℝ) (ht : t ∈ Ioo l r) :
        spectralSecondClassicalFlux ell R hR w a u t=P t :=
      spectralSecondClassicalFlux_eq ell R hR w a u P t (hl.trans ht.1).ne'
        (hpos t (hs ht)).ne' (hd t ht)
    refine ⟨(hd x ⟨hxl,hxr⟩).differentiableAt,?_,?_⟩
    · have hDc := spectralSecondDerivativeValue_continuousOn ell R l r hR hl hr.le
        w a u P (hw.mono hs) (ha.mono hs) (fun s hs' => hpos s (hs hs')) hPc
      exact (hDc.congr (fun t ht => (hd t ht).deriv)).continuousAt
        (Ioo_mem_nhds hxl hxr)
    · apply (hP x ⟨hxl,hxr⟩).congr_of_eventuallyEq
      filter_upwards [Ioo_mem_nhds hxl hxr] with t ht
      exact heq t ht
  exact ⟨fun x hx => (hlocal x hx).1.differentiableWithinAt,
    fun x hx => (hlocal x hx).2.1.continuousWithinAt,fun x hx => (hlocal x hx).2.2⟩

end DefocusingNLS

end OAI
