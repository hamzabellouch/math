import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralAnnulusFluxPrimitive
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralForcedClassicalFlux

namespace OAI

/-! Exterior classical fluxes from tests supported outside the core. -/

open Set MeasureTheory
open scoped ContDiff
namespace DefocusingNLS

theorem spectralSecond_forced_classical_annulus (ell : ℕ) (L R : ℝ)
    (hL : 0 ≤ L) (hR : 0 < R)
    (w a : SpectralHarmonicWeight R) (u : SpectralHarmonicPair ell R) (G : ℝ → ℂ)
    (hw : ContinuousOn w.density (Ioo L R)) (ha : ContinuousOn a.density (Ioo L R))
    (hpos : ∀ x ∈ Ioo L R, 0 < w.density x) (hG : ContinuousOn G (Ioo L R))
    (hF : LocallyIntegrableOn (spectralSecondFlux ell R w a u) (Ioo L R))
    (he : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo L R →
        (∫ x, deriv φ x • spectralSecondFlux ell R w a u x) = -(∫ x, φ x • G x)) :
    DifferentiableOn ℝ (spectralHarmonicRepresentative ell R hR u.snd) (Ioo L R) ∧
      ContinuousOn (deriv (spectralHarmonicRepresentative ell R hR u.snd)) (Ioo L R) ∧
      ∀ x ∈ Ioo L R, HasDerivAt (spectralSecondClassicalFlux ell R hR w a u) (G x) x := by
  have hlocal (x : ℝ) (hx : x ∈ Ioo L R) :
      DifferentiableAt ℝ (spectralHarmonicRepresentative ell R hR u.snd) x ∧
      ContinuousAt (deriv (spectralHarmonicRepresentative ell R hR u.snd)) x ∧
      HasDerivAt (spectralSecondClassicalFlux ell R hR w a u)
        (G x) x := by
    let l := (L+x)/2
    let r := (x+R)/2
    have hLl : L < l := by dsimp only [l]; linarith [hx.1]
    have hl : 0 < l := hL.trans_lt hLl
    have hxl : l < x := by dsimp only [l]; linarith [hx.1]
    have hxr : x < r := by dsimp only [r]; linarith [hx.2]
    have hr : r < R := by dsimp only [r]; linarith [hx.2]
    have hs : Ioo l r ⊆ Ioo L R := fun t ht => ⟨hLl.trans ht.1,ht.2.trans hr⟩
    obtain ⟨P,hP,hflux⟩ := spectralAnnulusFlux_primitive L R l r hLl (hxl.trans hxr) hr
      (spectralSecondFlux ell R w a u) G
      hF hG he
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
