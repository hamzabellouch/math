import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralChainScalarEquation
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralFirstTest
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralHarmonicScalarPairing
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralObservationZero

namespace OAI

/-! The first-channel derivative load is minus the leading second channel.
Tests will later be restricted to the exterior of the constrained core. -/

namespace DefocusingNLS
open scoped SchwartzMap

theorem spectralFirstTest_chain_equation (ell : ℕ) (R : ℝ) (hR : 0 < R)
    (w : SpectralHarmonicWeight R) (u : SpectralHarmonicPair ell R)
    (Q A : SpectralRadialL2 R →L[ℂ] SpectralRadialL2 R) (c ζ : ℂ)
    (B B' : ℂ × ℂ →L[ℂ] ℂ × ℂ) (z₀ z₁ : SpectralRadialObservationSpace R)
    (f : 𝓢(ℝ,ℂ))
    (he : spectralHarmonicPairComplexForm ell R w u (spectralFirstTest ell R f) =
      inner ℂ (spectralLowerOrderOperator ell R hR Q A c ζ B z₁ +
        spectralLowerOrderSlope ell R hR Q B' z₀) (spectralFirstTest ell R f)) :
    star (spectralHarmonicComplexForm ell R w u.fst (spectralHarmonicSmoothEmbedding ell R f)) =
      inner ℂ (spectralHarmonicValue ell R (spectralHarmonicSmoothEmbedding ell R f)) (Q z₁.1.1) +
      (c-ζ) * inner ℂ (spectralHarmonicValue ell R (spectralHarmonicSmoothEmbedding ell R f)) (Q z₁.1.2) +
      inner ℂ (spectralHarmonicDerivative ell R (spectralHarmonicSmoothEmbedding ell R f)) (A z₁.1.2) +
      star (f R) * (B z₁.2).1 -
      inner ℂ (spectralHarmonicValue ell R (spectralHarmonicSmoothEmbedding ell R f)) (Q z₀.1.2) +
      star (f R) * (B' z₀.2).1 := by
  have hs := congrArg star he
  rw [spectral_star_inner, inner_add_right, spectralLowerOrderOperator_inner,
    spectralLowerOrderSlope_inner] at hs
  change star (spectralHarmonicComplexForm ell R w u.fst (spectralHarmonicSmoothEmbedding ell R f) +
    spectralHarmonicComplexForm ell R w u.snd 0) = _ at hs
  have hz : spectralHarmonicComplexForm ell R w u.snd 0 = 0 := by
    simp only [spectralHarmonicComplexForm, map_zero, inner_zero_right, add_zero]
  rw [hz, add_zero] at hs
  unfold spectralWeakPairing at hs
  rw [spectralFirstTest_values, spectralFirstTest_derivatives, spectralFirstTest_traces] at hs
  simpa only [inner_zero_left, zero_add, zero_sub, add_zero, RCLike.inner_apply',
    sub_eq_add_neg, mul_neg, neg_mul, zero_mul, star_zero, starRingEnd_apply,
    neg_neg, neg_zero, add_assoc] using hs


end DefocusingNLS

end OAI
