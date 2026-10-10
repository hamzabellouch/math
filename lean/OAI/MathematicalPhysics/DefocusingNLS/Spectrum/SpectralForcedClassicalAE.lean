import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralAnnulusClassicalFlux
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralClassicalFluxAE

namespace OAI

/-! Identification almost everywhere of an inhomogeneous weak flux with its
classical representative; this also applies outside a constrained core. -/

open Set MeasureTheory
open scoped ContDiff
namespace DefocusingNLS

theorem spectralSecond_forced_classical_ae (ell : ℕ) (L R : ℝ)
    (hL : 0 ≤ L) (hR : 0 < R)
    (w a : SpectralHarmonicWeight R) (u : SpectralHarmonicPair ell R) (G : ℝ → ℂ)
    (hw : ContinuousOn w.density (Ioo L R)) (ha : ContinuousOn a.density (Ioo L R))
    (hpos : ∀ x ∈ Ioo L R, 0 < w.density x) (hG : ContinuousOn G (Ioo L R))
    (hF : LocallyIntegrableOn (spectralSecondFlux ell R w a u) (Ioo L R))
    (he : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo L R →
        (∫ x, deriv φ x • spectralSecondFlux ell R w a u x) = -(∫ x, φ x • G x)) :
    ∀ᵐ x, x ∈ Ioo L R →
      spectralSecondFlux ell R w a u x = spectralSecondClassicalFlux ell R hR w a u x := by
  apply ae_of_mem_of_ae_of_mem_inter_Ioo
  intro l r hl hr hlr
  obtain ⟨P,hP,hflux⟩ := spectralAnnulusFlux_primitive L R l r hl.1 hlr hr.2
    (spectralSecondFlux ell R w a u) G hF hG he
  have hs : Ioo l r ⊆ Ioo L R := fun x hx => ⟨hl.1.trans hx.1,hx.2.trans hr.2⟩
  have hlocal := spectralLocalFlux_classical_ae ell R l r hR (hL.trans_lt hl.1) hr.2.le
    w a u P (hw.mono hs) (ha.mono hs) (fun x hx => hpos x (hs hx))
    (fun x hx => (hP x hx).continuousAt.continuousWithinAt) hflux
  filter_upwards [hlocal] with x hx hxr
  exact hx hxr.2

end DefocusingNLS

end OAI
