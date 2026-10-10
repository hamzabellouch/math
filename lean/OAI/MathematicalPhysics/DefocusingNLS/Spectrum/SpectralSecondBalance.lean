import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPencilScalarEquation

namespace OAI

/-! Cancellation of the mass terms gives the exact weak flux balance. -/

open MeasureTheory
open scoped SchwartzMap
namespace DefocusingNLS

theorem spectralSecondTest_balance (ell : ℕ) (R : ℝ) (hR : 0 < R)
    (w a : SpectralHarmonicWeight R) (u : SpectralHarmonicPair ell R) (c ζ : ℂ)
    (B : ℂ × ℂ →L[ℂ] ℂ × ℂ) (f : 𝓢(ℝ,ℂ)) (hfR : f R=0)
    (he : spectralHarmonicPairComplexForm ell R w u (spectralSecondTest ell R f)=
      inner ℂ (spectralLowerOrderOperator ell R hR
        (spectralRadialWeightMultiplier R w) (spectralRadialWeightMultiplier R a) c ζ B
        (spectralHarmonicObservation ell R hR u)) (spectralSecondTest ell R f)) :
    (∫ r, star (deriv f r)*(w.density r • spectralHarmonicDerivative ell R u.snd r)
      ∂radialPressureMeasure R) +
    (((ell : ℝ)*(ell+10) : ℝ) : ℂ)*
      (∫ r, star (f r)*(w.density r • spectralHarmonicValue ell R u.snd r)
        ∂spectralAngularMeasure R) +
    (c-ζ)*(∫ r, star (f r)*(w.density r • spectralHarmonicValue ell R u.fst r)
      ∂radialPressureMeasure R) +
    (∫ r, star (deriv f r)*(a.density r • spectralHarmonicValue ell R u.fst r)
      ∂radialPressureMeasure R)=0 := by
  have h := spectralSecondTest_equation ell R hR w u
    (spectralRadialWeightMultiplier R w) (spectralRadialWeightMultiplier R a)
    c ζ B (spectralHarmonicObservation ell R hR u) f he
  rw [spectralHarmonicScalar_pairing] at h
  have hv (v : SpectralRadialL2 R) :
      inner ℂ (spectralHarmonicValue ell R (spectralHarmonicSmoothEmbedding ell R f))
        (spectralRadialWeightMultiplier R w v)=
      ∫ r, star (f r)*(w.density r • v r) ∂radialPressureMeasure R :=
    spectralL2ComplexMultiplier_pairing_test _ _ _ _ _ _ _ _
      (spectralHarmonicValue_smooth_ae ell R f)
  have hd (v : SpectralRadialL2 R) :
      inner ℂ (spectralHarmonicDerivative ell R (spectralHarmonicSmoothEmbedding ell R f))
        (spectralRadialWeightMultiplier R a v)=
      ∫ r, star (deriv f r)*(a.density r • v r) ∂radialPressureMeasure R :=
    spectralL2ComplexMultiplier_pairing_test _ _ _ _ _ _ _ _
      (spectralHarmonicDerivative_smooth_ae ell R f)
  rw [hv,hv,hd,hfR,star_zero,zero_mul,add_zero] at h
  change _ =
    (∫ r, star (f r)*(w.density r • spectralHarmonicValue ell R u.snd r)
      ∂radialPressureMeasure R)-
    (c-ζ)*(∫ r, star (f r)*(w.density r • spectralHarmonicValue ell R u.fst r)
      ∂radialPressureMeasure R)-
    (∫ r, star (deriv f r)*(a.density r • spectralHarmonicValue ell R u.fst r)
      ∂radialPressureMeasure R) at h
  linear_combination h

end DefocusingNLS

end OAI
