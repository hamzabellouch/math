import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralSecondFluxDerivative

namespace OAI

/-! The weak flux equals the flux of the classical radial representative. -/

open Set MeasureTheory
open scoped SchwartzMap
namespace DefocusingNLS

noncomputable def spectralSecondClassicalFlux (ell : ℕ) (R : ℝ) (hR : 0 < R)
    (w a : SpectralHarmonicWeight R) (u : SpectralHarmonicPair ell R) (x : ℝ) : ℂ :=
  (x : ℂ)^11*((w.density x : ℂ)*deriv (spectralHarmonicRepresentative ell R hR u.snd) x+
    (a.density x : ℂ)*spectralHarmonicRepresentative ell R hR u.fst x)

theorem spectralSecondDerivativeValue_continuousOn (ell : ℕ) (R l r : ℝ) (hR : 0 < R)
    (hl : 0 < l) (hr : r ≤ R) (w a : SpectralHarmonicWeight R)
    (u : SpectralHarmonicPair ell R) (P : ℝ → ℂ)
    (hw : ContinuousOn w.density (Ioo l r)) (ha : ContinuousOn a.density (Ioo l r))
    (hpos : ∀ x ∈ Ioo l r, 0 < w.density x) (hP : ContinuousOn P (Ioo l r)) :
    ContinuousOn (spectralSecondDerivativeValue ell R hR w a u P) (Ioo l r) := by
  have hs : Ioo l r ⊆ Ioo 0 R := fun t ht => ⟨hl.trans ht.1,ht.2.trans_le hr⟩
  exact ((hP.div (Complex.continuous_ofReal.continuousOn.pow 11)
    (fun t ht => pow_ne_zero _ (by exact_mod_cast (hl.trans ht.1).ne'))).sub
      ((Complex.continuous_ofReal.comp_continuousOn ha).mul
        ((spectralHarmonicRepresentative_continuousOn ell R hR u.fst).mono hs))).div
          (Complex.continuous_ofReal.comp_continuousOn hw)
          (fun t ht => by exact_mod_cast (hpos t ht).ne')

theorem spectralSecondClassicalFlux_eq (ell : ℕ) (R : ℝ) (hR : 0 < R)
    (w a : SpectralHarmonicWeight R) (u : SpectralHarmonicPair ell R) (P : ℝ → ℂ)
    (x : ℝ) (hx : x ≠ 0) (hw : w.density x ≠ 0)
    (hd : HasDerivAt (spectralHarmonicRepresentative ell R hR u.snd)
      (spectralSecondDerivativeValue ell R hR w a u P x) x) :
    spectralSecondClassicalFlux ell R hR w a u x=P x := by
  unfold spectralSecondClassicalFlux
  rw [hd.deriv]
  dsimp only [spectralSecondDerivativeValue]
  have hx' : (x : ℂ) ≠ 0 := by exact_mod_cast hx
  have hw' : (w.density x : ℂ) ≠ 0 := by exact_mod_cast hw
  field_simp
  ring

theorem spectralSecond_classical (ell : ℕ) (R : ℝ) (hR : 0 < R)
    (w a : SpectralHarmonicWeight R) (u : SpectralHarmonicPair ell R) (c ζ : ℂ)
    (B : ℂ × ℂ →L[ℂ] ℂ × ℂ)
    (hw : ContinuousOn w.density (Ioo 0 R)) (ha : ContinuousOn a.density (Ioo 0 R))
    (hpos : ∀ x ∈ Ioo 0 R, 0 < w.density x)
    (he : ∀ f : 𝓢(ℝ,ℂ),
      spectralHarmonicPairComplexForm ell R w u (spectralSecondTest ell R f)=
      inner ℂ (spectralLowerOrderOperator ell R hR
        (spectralRadialWeightMultiplier R w) (spectralRadialWeightMultiplier R a) c ζ B
        (spectralHarmonicObservation ell R hR u)) (spectralSecondTest ell R f)) :
    DifferentiableOn ℝ (spectralHarmonicRepresentative ell R hR u.snd) (Ioo 0 R) ∧
      ContinuousOn (deriv (spectralHarmonicRepresentative ell R hR u.snd)) (Ioo 0 R) ∧
      ∀ x ∈ Ioo 0 R, HasDerivAt (spectralSecondClassicalFlux ell R hR w a u)
        (spectralSecondContinuousSource ell R hR w u c ζ x) x := by
  have hlocal (x : ℝ) (hx : x ∈ Ioo 0 R) :
      DifferentiableAt ℝ (spectralHarmonicRepresentative ell R hR u.snd) x ∧
      ContinuousAt (deriv (spectralHarmonicRepresentative ell R hR u.snd)) x ∧
      HasDerivAt (spectralSecondClassicalFlux ell R hR w a u)
        (spectralSecondContinuousSource ell R hR w u c ζ x) x := by
    let l := x/2
    let r := (x+R)/2
    have hl : 0 < l := by dsimp only [l]; linarith [hx.1]
    have hxl : l < x := by dsimp only [l]; linarith [hx.1]
    have hxr : x < r := by dsimp only [r]; linarith [hx.2]
    have hr : r < R := by dsimp only [r]; linarith [hx.2]
    have hs : Ioo l r ⊆ Ioo 0 R := fun t ht => ⟨hl.trans ht.1,ht.2.trans hr⟩
    obtain ⟨P,hP,hflux⟩ := spectralSecondFlux_primitive ell R l r hR hl (hxl.trans hxr) hr
      w a u c ζ B hw ha he
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
