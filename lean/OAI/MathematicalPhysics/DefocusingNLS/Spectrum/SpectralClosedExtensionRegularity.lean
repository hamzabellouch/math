import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralClosedClassicalExtension

namespace OAI

/-! Continuity of the endpoint derivatives supplied by the weak-flux extension. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem spectralSecondDerivativeValue_continuousOn_closed (ell : ℕ) (R δ : ℝ) (hR : 0 < R)
    (hδ : 0 < δ) (w a : SpectralHarmonicWeight R) (u : SpectralHarmonicPair ell R)
    (P : ℝ → ℂ) (hP : Continuous P) (hw : ContinuousOn w.density (Icc δ R))
    (ha : ContinuousOn a.density (Icc δ R))
    (hpos : ∀ x ∈ Icc δ R, 0 < w.density x) :
    ContinuousOn (spectralSecondDerivativeValue ell R hR w a u P) (Icc δ R) :=
  ((hP.continuousOn.div (Complex.continuous_ofReal.continuousOn.pow 11)
    (fun x hx => pow_ne_zero _ (by exact_mod_cast (hδ.trans_le hx.1).ne'))).sub
    ((Complex.continuous_ofReal.comp_continuousOn ha).mul
      (spectralHarmonicRepresentative_continuousOn_closed ell R δ hR hδ u.fst))).div
        (Complex.continuous_ofReal.comp_continuousOn hw)
        (fun x hx => by exact_mod_cast (hpos x hx).ne')

theorem spectralSecond_closedExtension_C1 (ell : ℕ) (R δ : ℝ) (hR : 0 < R)
    (hδ : 0 < δ) (hδR : δ < R)
    (w a : SpectralHarmonicWeight R) (u : SpectralHarmonicPair ell R) (P : ℝ → ℂ)
    (hP : Continuous P) (hw : ContinuousOn w.density (Icc δ R))
    (ha : ContinuousOn a.density (Icc δ R))
    (hpos : ∀ x ∈ Icc δ R, 0 < w.density x)
    (hflux : ∀ᵐ x, x ∈ Icc δ R → spectralSecondFlux ell R w a u x=P x) :
    ∃ U : ℝ → ℂ, Continuous U ∧ ContinuousOn (deriv U) (Icc δ R) ∧
      (∀ x ∈ Icc δ R, HasDerivAt U (spectralSecondDerivativeValue ell R hR w a u P x) x) ∧
      EqOn U (spectralHarmonicRepresentative ell R hR u.snd) (Icc δ R) ∧
      (R : ℂ)^11*((w.density R : ℂ)*deriv U R+
        (a.density R : ℂ)*spectralHarmonicRepresentative ell R hR u.fst R)=P R := by
  obtain ⟨U,hU,hd,he,hB⟩ := spectralSecond_closedExtension ell R δ hR hδ hδR
    w a u P hP hw ha hpos hflux
  refine ⟨U,hU,?_,hd,he,hB⟩
  apply (spectralSecondDerivativeValue_continuousOn_closed ell R δ hR hδ w a u P hP hw ha hpos).congr
  exact fun x hx => (hd x hx).deriv

end DefocusingNLS

end OAI
