import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralChainFirstBalance
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralChainFluxBalance
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRepresentativeTrace

namespace OAI

/-! Boundary terms of the exact weak first-chain equations. -/

open MeasureTheory
open scoped SchwartzMap
namespace DefocusingNLS

theorem spectralSecondTest_chain_boundaryBalance (ell : ℕ) (R : ℝ) (hR : 0 < R)
    (w a : SpectralHarmonicWeight R) (u₀ u₁ : SpectralHarmonicPair ell R) (c ζ : ℂ)
    (B B' : ℂ × ℂ →L[ℂ] ℂ × ℂ) (f : 𝓢(ℝ,ℂ))
    (he : spectralHarmonicPairComplexForm ell R w u₁ (spectralSecondTest ell R f) =
      inner ℂ (spectralLowerOrderOperator ell R hR
        (spectralRadialWeightMultiplier R w) (spectralRadialWeightMultiplier R a) c ζ B
        (spectralHarmonicObservation ell R hR u₁) +
        spectralLowerOrderSlope ell R hR (spectralRadialWeightMultiplier R w) B'
          (spectralHarmonicObservation ell R hR u₀)) (spectralSecondTest ell R f)) :
    (∫ r, star (deriv f r)*(w.density r • spectralHarmonicDerivative ell R u₁.snd r)
      ∂radialPressureMeasure R) +
    (((ell : ℝ)*(ell+10) : ℝ) : ℂ)*
      (∫ r, star (f r)*(w.density r • spectralHarmonicValue ell R u₁.snd r)
        ∂spectralAngularMeasure R) +
    (c-ζ)*(∫ r, star (f r)*(w.density r • spectralHarmonicValue ell R u₁.fst r)
      ∂radialPressureMeasure R) +
    (∫ r, star (deriv f r)*(a.density r • spectralHarmonicValue ell R u₁.fst r)
      ∂radialPressureMeasure R) =
    star (f R) * ((B (spectralHarmonicPairTraces ell R hR u₁)).2 +
      (B' (spectralHarmonicPairTraces ell R hR u₀)).2) +
    (∫ r, star (f r)*(w.density r • spectralHarmonicValue ell R u₀.fst r)
      ∂radialPressureMeasure R) := by
  have h := spectralSecondTest_chain_equation ell R hR w u₁
    (spectralRadialWeightMultiplier R w) (spectralRadialWeightMultiplier R a)
    c ζ B B' (spectralHarmonicObservation ell R hR u₀)
    (spectralHarmonicObservation ell R hR u₁) f he
  rw [spectralHarmonicScalar_pairing, spectralHarmonicObservation_coordinates ell R hR u₁,
    spectralHarmonicObservation_coordinates ell R hR u₀] at h
  have hv (v : SpectralRadialL2 R) :
      inner ℂ (spectralHarmonicValue ell R (spectralHarmonicSmoothEmbedding ell R f))
        (spectralRadialWeightMultiplier R w v) =
      ∫ r, star (f r)*(w.density r • v r) ∂radialPressureMeasure R :=
    spectralL2ComplexMultiplier_pairing_test _ _ _ _ _ _ _ _
      (spectralHarmonicValue_smooth_ae ell R f)
  have hd (v : SpectralRadialL2 R) :
      inner ℂ (spectralHarmonicDerivative ell R (spectralHarmonicSmoothEmbedding ell R f))
        (spectralRadialWeightMultiplier R a v) =
      ∫ r, star (deriv f r)*(a.density r • v r) ∂radialPressureMeasure R :=
    spectralL2ComplexMultiplier_pairing_test _ _ _ _ _ _ _ _
      (spectralHarmonicDerivative_smooth_ae ell R f)
  rw [hv (spectralHarmonicValue ell R u₁.snd)] at h
  rw [hv (spectralHarmonicValue ell R u₁.fst)] at h
  rw [hd (spectralHarmonicValue ell R u₁.fst)] at h
  rw [hv (spectralHarmonicValue ell R u₀.fst)] at h
  rw [← spectralHarmonicRepresentative_trace ell R hR u₁,
    ← spectralHarmonicRepresentative_trace ell R hR u₀]
  linear_combination h

theorem spectralFirstTest_chain_boundaryBalance (ell : ℕ) (R : ℝ) (hR : 0 < R)
    (w a : SpectralHarmonicWeight R) (u₀ u₁ : SpectralHarmonicPair ell R) (c ζ : ℂ)
    (B B' : ℂ × ℂ →L[ℂ] ℂ × ℂ) (f : 𝓢(ℝ,ℂ))
    (he : spectralHarmonicPairComplexForm ell R w u₁ (spectralFirstTest ell R f) =
      inner ℂ (spectralLowerOrderOperator ell R hR
        (spectralRadialWeightMultiplier R w) (spectralRadialWeightMultiplier R a) c ζ B
        (spectralHarmonicObservation ell R hR u₁) +
        spectralLowerOrderSlope ell R hR (spectralRadialWeightMultiplier R w) B'
          (spectralHarmonicObservation ell R hR u₀)) (spectralFirstTest ell R f)) :
    (∫ r, star (deriv f r)*(w.density r • spectralHarmonicDerivative ell R u₁.fst r)
      ∂radialPressureMeasure R) +
    (((ell : ℝ)*(ell+10) : ℝ) : ℂ)*
      (∫ r, star (f r)*(w.density r • spectralHarmonicValue ell R u₁.fst r)
        ∂spectralAngularMeasure R) -
    (c-ζ)*(∫ r, star (f r)*(w.density r • spectralHarmonicValue ell R u₁.snd r)
      ∂radialPressureMeasure R) -
    (∫ r, star (deriv f r)*(a.density r • spectralHarmonicValue ell R u₁.snd r)
      ∂radialPressureMeasure R) =
    star (f R) * ((B (spectralHarmonicPairTraces ell R hR u₁)).1 +
      (B' (spectralHarmonicPairTraces ell R hR u₀)).1) -
    (∫ r, star (f r)*(w.density r • spectralHarmonicValue ell R u₀.snd r)
      ∂radialPressureMeasure R) := by
  have h := spectralFirstTest_chain_equation ell R hR w u₁
    (spectralRadialWeightMultiplier R w) (spectralRadialWeightMultiplier R a)
    c ζ B B' (spectralHarmonicObservation ell R hR u₀)
    (spectralHarmonicObservation ell R hR u₁) f he
  rw [spectralHarmonicScalar_pairing, spectralHarmonicObservation_coordinates ell R hR u₁,
    spectralHarmonicObservation_coordinates ell R hR u₀] at h
  have hv (v : SpectralRadialL2 R) :
      inner ℂ (spectralHarmonicValue ell R (spectralHarmonicSmoothEmbedding ell R f))
        (spectralRadialWeightMultiplier R w v) =
      ∫ r, star (f r)*(w.density r • v r) ∂radialPressureMeasure R :=
    spectralL2ComplexMultiplier_pairing_test _ _ _ _ _ _ _ _
      (spectralHarmonicValue_smooth_ae ell R f)
  have hd (v : SpectralRadialL2 R) :
      inner ℂ (spectralHarmonicDerivative ell R (spectralHarmonicSmoothEmbedding ell R f))
        (spectralRadialWeightMultiplier R a v) =
      ∫ r, star (deriv f r)*(a.density r • v r) ∂radialPressureMeasure R :=
    spectralL2ComplexMultiplier_pairing_test _ _ _ _ _ _ _ _
      (spectralHarmonicDerivative_smooth_ae ell R f)
  rw [hv (spectralHarmonicValue ell R u₁.fst)] at h
  rw [hv (spectralHarmonicValue ell R u₁.snd)] at h
  rw [hd (spectralHarmonicValue ell R u₁.snd)] at h
  rw [hv (spectralHarmonicValue ell R u₀.snd)] at h
  rw [← spectralHarmonicRepresentative_trace ell R hR u₁,
    ← spectralHarmonicRepresentative_trace ell R hR u₀]
  linear_combination h

end DefocusingNLS

end OAI
