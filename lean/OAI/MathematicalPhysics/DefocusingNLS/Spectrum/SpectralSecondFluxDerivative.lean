import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralSecondFluxPrimitive
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRadialLocalDerivative

namespace OAI

/-! Recover the classical second derivative coordinate from its continuous weighted flux. -/

open Set MeasureTheory
namespace DefocusingNLS

noncomputable def spectralSecondDerivativeValue (ell : ℕ) (R : ℝ) (hR : 0 < R)
    (w a : SpectralHarmonicWeight R) (u : SpectralHarmonicPair ell R)
    (P : ℝ → ℂ) (x : ℝ) : ℂ :=
  (P x/(x : ℂ)^11 - (a.density x : ℂ)*spectralHarmonicRepresentative ell R hR u.fst x)/
    (w.density x : ℂ)

theorem spectralSecondFlux_hasDerivAt (ell : ℕ) (R l r : ℝ) (hR : 0 < R)
    (hl : 0 < l) (hr : r ≤ R) (w a : SpectralHarmonicWeight R)
    (u : SpectralHarmonicPair ell R) (P : ℝ → ℂ)
    (hw : ContinuousOn w.density (Ioo l r)) (ha : ContinuousOn a.density (Ioo l r))
    (hpos : ∀ x ∈ Ioo l r, 0 < w.density x) (hP : ContinuousOn P (Ioo l r))
    (hflux : ∀ᵐ x, x ∈ Ioo l r → spectralSecondFlux ell R w a u x=P x)
    (x : ℝ) (hx : x ∈ Ioo l r) :
    HasDerivAt (spectralHarmonicRepresentative ell R hR u.snd)
      (spectralSecondDerivativeValue ell R hR w a u P x) x := by
  have hs : Ioo l r ⊆ Ioo 0 R := fun t ht => ⟨hl.trans ht.1,ht.2.trans_le hr⟩
  have hn (t : ℝ) (ht : t ∈ Ioo l r) : (t : ℂ)^11 ≠ 0 :=
    pow_ne_zero _ (by exact_mod_cast (hl.trans ht.1).ne')
  have hm (t : ℝ) (ht : t ∈ Ioo l r) : (w.density t : ℂ) ≠ 0 :=
    by exact_mod_cast (hpos t ht).ne'
  have hF : ContinuousOn (spectralSecondDerivativeValue ell R hR w a u P) (Ioo l r) :=
    ((hP.div (Complex.continuous_ofReal.continuousOn.pow 11) hn).sub
      ((Complex.continuous_ofReal.comp_continuousOn ha).mul
        ((spectralHarmonicRepresentative_continuousOn ell R hR u.fst).mono hs))).div
          (Complex.continuous_ofReal.comp_continuousOn hw) hm
  have hf := (ae_restrict_iff' measurableSet_Icc).mp
    (spectralHarmonicRepresentative_ae ell R hR u.fst)
  apply spectralRadialRepresentative_hasDerivAt_local R l r hR hl hr
    (spectralHarmonicRadialForget ell R u.snd) _ hF _ x hx
  filter_upwards [hflux,hf] with t ht hf htmem
  have hft := hf (Ioo_subset_Icc_self (hs htmem))
  change spectralHarmonicDerivative ell R u.snd t = _
  apply (eq_div_iff (hm t htmem)).mpr
  have he : (w.density t : ℂ)*spectralHarmonicDerivative ell R u.snd t +
      (a.density t : ℂ)*spectralHarmonicRepresentative ell R hR u.fst t = P t/(t : ℂ)^11 := by
    apply (eq_div_iff (hn t htmem)).mpr
    simpa only [spectralSecondFlux,Complex.real_smul,← hft,mul_comm] using ht htmem
  linear_combination he

end DefocusingNLS

end OAI
