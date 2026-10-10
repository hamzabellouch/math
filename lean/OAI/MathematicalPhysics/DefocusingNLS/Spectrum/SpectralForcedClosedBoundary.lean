import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralForcedClassicalAE
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCutoffFluxTrace
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralEndpointTest

namespace OAI

/-! Recover the finite endpoint trace of a continuously forced weak flux. -/

open Set MeasureTheory
open scoped SchwartzMap ContDiff
namespace DefocusingNLS

theorem spectralForced_closedBoundary (ell : ℕ) (L R δ : ℝ)
    (hL : 0 ≤ L) (hR : 0 < R) (hLδ : L < δ) (hδR : δ < R)
    (w a : SpectralHarmonicWeight R) (u : SpectralHarmonicPair ell R) (G : ℝ → ℂ) (β : ℂ)
    (hw : ContinuousOn w.density (Ioo L R)) (ha : ContinuousOn a.density (Ioo L R))
    (hpos : ∀ x ∈ Ioo L R, 0 < w.density x)
    (hG : ContinuousOn G (Ioo L R)) (hGc : ContinuousOn G (Icc δ R))
    (hF : LocallyIntegrableOn (spectralSecondFlux ell R w a u) (Ioo L R))
    (he : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo L R →
        (∫ x, deriv φ x • spectralSecondFlux ell R w a u x) = -(∫ x, φ x • G x))
    (hB : ∀ f : 𝓢(ℝ,ℂ), f R = 1 → (∀ x ≤ δ, f x = 0) →
      (∫ x in (0 : ℝ)..R, star (deriv f x)*spectralSecondFlux ell R w a u x) =
        β - (∫ x in (0 : ℝ)..R, star (f x)*G x)) :
    ∃ P : ℝ → ℂ, Continuous P ∧
      (∀ x ∈ Icc δ R, HasDerivAt P (G x) x) ∧
      EqOn (spectralSecondClassicalFlux ell R hR w a u) P (Ioo δ R) ∧
      (∀ᵐ x, x ∈ Icc δ R → spectralSecondFlux ell R w a u x = P x) ∧ P R = β := by
  have hs : Ioo δ R ⊆ Ioo L R := fun x hx => ⟨hLδ.trans hx.1,hx.2⟩
  have hclass := (spectralSecond_forced_classical_annulus ell L R hL hR w a u G
    hw ha hpos hG hF he).2.2
  have hae := spectralSecond_forced_classical_ae ell L R hL hR w a u G
    hw ha hpos hG hF he
  obtain ⟨P,hP,hd,hEq,hFP⟩ := spectralClosedFlux_ae_primitive δ R hδR
    (spectralSecondFlux ell R w a u) (spectralSecondClassicalFlux ell R hR w a u) G hGc
    (fun x hx => hclass x (hs hx)) (by
      filter_upwards [hae] with x hx hxr
      exact hx (hs hxr))
  refine ⟨P,hP,hd,hEq,hFP,?_⟩
  obtain ⟨f,hfR,hf,hdf⟩ := spectralEndpointTest δ R hδR
  exact spectralCutoffFlux_trace δ R (hL.trans_lt hLδ).le hδR
    (spectralSecondFlux ell R w a u) G P G hP hGc hd hFP
    (Filter.Eventually.of_forall (fun _ _ => rfl)) f hfR hf hdf β (hB f hfR hf)

end DefocusingNLS

end OAI
