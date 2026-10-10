import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralLowerOrderDerivative
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralSecondTest

namespace OAI

/-! The derivative load in the second radial equation is precisely the
leading first channel, together with the differentiated boundary flux. -/

namespace DefocusingNLS
open scoped SchwartzMap

theorem spectralWeakOperatorSlope_inner {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (V : E →L[ℂ] F × F) (T : E →L[ℂ] ℂ × ℂ)
    (Q : F →L[ℂ] F) (B : ℂ × ℂ →L[ℂ] ℂ × ℂ)
    (θ : E) (z : (F × F) × (ℂ × ℂ)) :
    inner ℂ θ (spectralWeakOperatorSlope V T Q B z) =
      -(inner ℂ (V θ).1 (Q z.1.2) - inner ℂ (V θ).2 (Q z.1.1)) +
        (inner ℂ (T θ).1 (B z.2).1 + inner ℂ (T θ).2 (B z.2).2) := by
  change inner ℂ θ (-spectralPairRiesz V (Q z.1.2, Q (-z.1.1)) +
    spectralPairRiesz T (B z.2)) = _
  rw [inner_add_right, inner_neg_right, spectralPairRiesz_inner, spectralPairRiesz_inner,
    map_neg, inner_neg_right]
  ring

theorem spectralLowerOrderSlope_inner (ell : ℕ) (R : ℝ) (hR : 0 < R)
    (Q : SpectralRadialL2 R →L[ℂ] SpectralRadialL2 R)
    (B : ℂ × ℂ →L[ℂ] ℂ × ℂ)
    (θ : SpectralHarmonicPair ell R) (z : SpectralRadialObservationSpace R) :
    inner ℂ θ (spectralLowerOrderSlope ell R hR Q B z) =
      -(inner ℂ (spectralHarmonicPairValues ell R θ).1 (Q z.1.2) -
        inner ℂ (spectralHarmonicPairValues ell R θ).2 (Q z.1.1)) +
      (inner ℂ (spectralHarmonicPairTraces ell R hR θ).1 (B z.2).1 +
        inner ℂ (spectralHarmonicPairTraces ell R hR θ).2 (B z.2).2) :=
  spectralWeakOperatorSlope_inner _ _ _ _ _ _

theorem spectralSecondTest_chain_equation (ell : ℕ) (R : ℝ) (hR : 0 < R)
    (w : SpectralHarmonicWeight R) (u : SpectralHarmonicPair ell R)
    (Q A : SpectralRadialL2 R →L[ℂ] SpectralRadialL2 R) (c ζ : ℂ)
    (B B' : ℂ × ℂ →L[ℂ] ℂ × ℂ) (z₀ z₁ : SpectralRadialObservationSpace R)
    (f : 𝓢(ℝ,ℂ))
    (he : spectralHarmonicPairComplexForm ell R w u (spectralSecondTest ell R f) =
      inner ℂ (spectralLowerOrderOperator ell R hR Q A c ζ B z₁ +
        spectralLowerOrderSlope ell R hR Q B' z₀) (spectralSecondTest ell R f)) :
    star (spectralHarmonicComplexForm ell R w u.snd (spectralHarmonicSmoothEmbedding ell R f)) =
      inner ℂ (spectralHarmonicValue ell R (spectralHarmonicSmoothEmbedding ell R f)) (Q z₁.1.2) -
      (c-ζ) * inner ℂ (spectralHarmonicValue ell R (spectralHarmonicSmoothEmbedding ell R f)) (Q z₁.1.1) -
      inner ℂ (spectralHarmonicDerivative ell R (spectralHarmonicSmoothEmbedding ell R f)) (A z₁.1.1) +
      star (f R) * (B z₁.2).2 +
      inner ℂ (spectralHarmonicValue ell R (spectralHarmonicSmoothEmbedding ell R f)) (Q z₀.1.1) +
      star (f R) * (B' z₀.2).2 := by
  have hs := congrArg star he
  rw [spectral_star_inner, inner_add_right, spectralLowerOrderOperator_inner,
    spectralLowerOrderSlope_inner] at hs
  change star (spectralHarmonicComplexForm ell R w u.fst 0 +
    spectralHarmonicComplexForm ell R w u.snd (spectralHarmonicSmoothEmbedding ell R f)) = _ at hs
  have hz : spectralHarmonicComplexForm ell R w u.fst 0 = 0 := by
    simp only [spectralHarmonicComplexForm, map_zero, inner_zero_right, add_zero]
  rw [hz, zero_add] at hs
  unfold spectralWeakPairing at hs
  rw [spectralSecondTest_values, spectralSecondTest_derivatives, spectralSecondTest_traces] at hs
  simpa only [inner_zero_left, zero_add, zero_sub, add_zero, RCLike.inner_apply',
    sub_eq_add_neg, mul_neg, neg_mul, zero_mul, star_zero, starRingEnd_apply,
    neg_neg, add_assoc] using hs

end DefocusingNLS

end OAI
