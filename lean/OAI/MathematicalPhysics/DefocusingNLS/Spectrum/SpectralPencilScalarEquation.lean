import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralSecondTest

namespace OAI

/-! Every limiting pencil kernel vector satisfies the second scalar equation across the core. -/

open scoped SchwartzMap
namespace DefocusingNLS.SpectralPenaltyFamily
variable {R l : ℝ}

theorem limitPencil_second_equation (s : SpectralPenaltyFamily R l) (ell : ℕ)
    (hl : 0 < l) (hlR : l < R)
    (Q A : SpectralRadialL2 R →L[ℂ] SpectralRadialL2 R) (c ζ : ℂ)
    (B : ℂ × ℂ →L[ℂ] ℂ × ℂ) (z : SpectralRadialObservationSpace R)
    (hz : s.limitPencil ell hl hlR
      (spectralLowerOrderOperator ell R (hl.trans hlR) Q A c ζ B) z=z) :
    ∃ u : SpectralHarmonicPair ell R, u ∈ spectralHarmonicCoreSubspace ell R l ∧
      spectralHarmonicObservation ell R (hl.trans hlR) u=z ∧
      ∀ f : 𝓢(ℝ,ℂ),
        star (spectralHarmonicComplexForm ell R s.limitWeight u.snd
          (spectralHarmonicSmoothEmbedding ell R f))=
          inner ℂ (spectralHarmonicValue ell R (spectralHarmonicSmoothEmbedding ell R f)) (Q z.1.2)-
          (c-ζ)*inner ℂ (spectralHarmonicValue ell R (spectralHarmonicSmoothEmbedding ell R f)) (Q z.1.1)-
          inner ℂ (spectralHarmonicDerivative ell R (spectralHarmonicSmoothEmbedding ell R f)) (A z.1.1)+
          star (f R)*(B z.2).2 := by
  obtain ⟨u,hu,hobs,hweak⟩ := (s.limitPencil_complex_variational ell hl hlR _ z).mp hz
  refine ⟨u,hu,hobs,fun f => ?_⟩
  exact spectralSecondTest_equation ell R (hl.trans hlR) s.limitWeight u Q A c ζ B z f
    (hweak ⟨spectralSecondTest ell R f,spectralSecondTest_core ell R l f⟩)

end DefocusingNLS.SpectralPenaltyFamily

end OAI
