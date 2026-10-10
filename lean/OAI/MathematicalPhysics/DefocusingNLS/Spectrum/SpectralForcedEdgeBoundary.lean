import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralForcedClosedBoundary

namespace OAI

/-! When the source is continuous at the constrained core, the flux extends
to that core as well as to the outer boundary. -/

open Set MeasureTheory
open scoped SchwartzMap ContDiff
namespace DefocusingNLS

theorem spectralForced_closedBoundary_at_edge (ell : ℕ) (L R : ℝ)
    (hL : 0 ≤ L) (hR : 0 < R) (hLR : L < R)
    (w a : SpectralHarmonicWeight R) (u : SpectralHarmonicPair ell R) (G : ℝ → ℂ) (β : ℂ)
    (hw : ContinuousOn w.density (Ioo L R)) (ha : ContinuousOn a.density (Ioo L R))
    (hpos : ∀ x ∈ Ioo L R, 0 < w.density x)
    (hG : ContinuousOn G (Ioo L R)) (hGc : ContinuousOn G (Icc L R))
    (hF : LocallyIntegrableOn (spectralSecondFlux ell R w a u) (Ioo L R))
    (he : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo L R →
        (∫ x, deriv φ x • spectralSecondFlux ell R w a u x) = -(∫ x, φ x • G x))
    (hB : ∀ f : 𝓢(ℝ,ℂ), f R = 1 → (∀ x ≤ L, f x = 0) →
      (∫ x in (0 : ℝ)..R, star (deriv f x)*spectralSecondFlux ell R w a u x) =
        β - (∫ x in (0 : ℝ)..R, star (f x)*G x)) :
    ∃ P : ℝ → ℂ, Continuous P ∧
      (∀ x ∈ Icc L R, HasDerivAt P (G x) x) ∧
      EqOn (spectralSecondClassicalFlux ell R hR w a u) P (Ioo L R) ∧
      (∀ᵐ x, x ∈ Icc L R → spectralSecondFlux ell R w a u x = P x) ∧ P R = β := by
  have hclass := (spectralSecond_forced_classical_annulus ell L R hL hR w a u G
    hw ha hpos hG hF he).2.2
  have hae := spectralSecond_forced_classical_ae ell L R hL hR w a u G
    hw ha hpos hG hF he
  obtain ⟨P,hP,hd,hEq,hFP⟩ := spectralClosedFlux_ae_primitive L R hLR
    (spectralSecondFlux ell R w a u) (spectralSecondClassicalFlux ell R hR w a u) G hGc
    (hclass) hae
  refine ⟨P,hP,hd,hEq,hFP,?_⟩
  obtain ⟨f,hfR,hf,hdf⟩ := spectralEndpointTest L R hLR
  exact spectralCutoffFlux_trace L R hL hLR
    (spectralSecondFlux ell R w a u) G P G hP hGc hd hFP
    (Filter.Eventually.of_forall (fun _ _ => rfl)) f hfR hf hdf β (hB f hfR hf)

end DefocusingNLS

end OAI
