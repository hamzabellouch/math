import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralClosedC1
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralClosedSource
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralSecondClassicalFlux

namespace OAI

/-! A continuous weak flux supplies the derivative at the outer endpoint. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem spectralSecond_closedExtension (ell : ℕ) (R δ : ℝ) (hR : 0 < R)
    (hδ : 0 < δ) (hδR : δ < R)
    (w a : SpectralHarmonicWeight R) (u : SpectralHarmonicPair ell R) (P : ℝ → ℂ)
    (hP : Continuous P) (hw : ContinuousOn w.density (Icc δ R))
    (ha : ContinuousOn a.density (Icc δ R))
    (hpos : ∀ x ∈ Icc δ R, 0 < w.density x)
    (hflux : ∀ᵐ x, x ∈ Icc δ R → spectralSecondFlux ell R w a u x=P x) :
    ∃ U : ℝ → ℂ, Continuous U ∧
      (∀ x ∈ Icc δ R, HasDerivAt U (spectralSecondDerivativeValue ell R hR w a u P x) x) ∧
      EqOn U (spectralHarmonicRepresentative ell R hR u.snd) (Icc δ R) ∧
      (R : ℂ)^11*((w.density R : ℂ)*deriv U R+
        (a.density R : ℂ)*spectralHarmonicRepresentative ell R hR u.fst R)=P R := by
  have hs := Ioo_subset_Icc_self (a := δ) (b := R)
  have hD : ContinuousOn (spectralSecondDerivativeValue ell R hR w a u P) (Icc δ R) :=
    ((hP.continuousOn.div (Complex.continuous_ofReal.continuousOn.pow 11)
      (fun x hx => pow_ne_zero _ (by exact_mod_cast (hδ.trans_le hx.1).ne'))).sub
      ((Complex.continuous_ofReal.comp_continuousOn ha).mul
        (spectralHarmonicRepresentative_continuousOn_closed ell R δ hR hδ u.fst))).div
          (Complex.continuous_ofReal.comp_continuousOn hw)
          (fun x hx => by exact_mod_cast (hpos x hx).ne')
  have hder (x : ℝ) (hx : x ∈ Ioo δ R) :
      HasDerivAt (spectralHarmonicRepresentative ell R hR u.snd)
        (spectralSecondDerivativeValue ell R hR w a u P x) x := by
    apply spectralSecondFlux_hasDerivAt ell R δ R hR hδ le_rfl w a u P
      (hw.mono hs) (ha.mono hs) (fun x hx => hpos x (hs hx)) hP.continuousOn _ x hx
    filter_upwards [hflux] with x hx hxr
    exact hx (hs hxr)
  obtain ⟨U,hU,hd,heq⟩ := spectralClosedC1_extension δ R hδR
    (spectralHarmonicRepresentative ell R hR u.snd)
    (spectralSecondDerivativeValue ell R hR w a u P)
    (spectralHarmonicRepresentative_continuousOn_closed ell R δ hR hδ u.snd) hD hder
  refine ⟨U,hU,hd,heq,?_⟩
  rw [(hd R ⟨hδR.le,le_rfl⟩).deriv]
  dsimp only [spectralSecondDerivativeValue]
  have hn : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  have hm : (w.density R : ℂ) ≠ 0 := by exact_mod_cast (hpos R ⟨hδR.le,le_rfl⟩).ne'
  field_simp
  ring

end DefocusingNLS

end OAI
