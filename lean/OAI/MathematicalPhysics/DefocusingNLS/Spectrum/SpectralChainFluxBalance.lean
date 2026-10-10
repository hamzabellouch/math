import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralChainScalarEquation
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRadialFluxIdentity
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralObservationZero

namespace OAI

/-! The exact weak first-chain equation has the expected inhomogeneous
weighted flux balance. -/

open MeasureTheory
open scoped SchwartzMap
namespace DefocusingNLS

theorem spectralSecondTest_chain_balance (ell : ℕ) (R : ℝ) (hR : 0 < R)
    (w a : SpectralHarmonicWeight R) (u₀ u₁ : SpectralHarmonicPair ell R) (c ζ : ℂ)
    (B B' : ℂ × ℂ →L[ℂ] ℂ × ℂ) (f : 𝓢(ℝ,ℂ)) (hfR : f R = 0)
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
    ∫ r, star (f r)*(w.density r • spectralHarmonicValue ell R u₀.fst r)
      ∂radialPressureMeasure R := by
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
  simp only [hfR, star_zero, zero_mul, add_zero] at h
  change _ =
    (∫ r, star (f r)*(w.density r • spectralHarmonicValue ell R u₁.snd r)
      ∂radialPressureMeasure R) -
    (c-ζ)*(∫ r, star (f r)*(w.density r • spectralHarmonicValue ell R u₁.fst r)
      ∂radialPressureMeasure R) -
    (∫ r, star (deriv f r)*(a.density r • spectralHarmonicValue ell R u₁.fst r)
      ∂radialPressureMeasure R) +
    (∫ r, star (f r)*(w.density r • spectralHarmonicValue ell R u₀.fst r)
      ∂radialPressureMeasure R) at h
  linear_combination h

theorem spectralSecondChain_flux_balance (ell : ℕ) (R : ℝ) (hR : 0 < R)
    (w a : SpectralHarmonicWeight R) (u₀ u₁ : SpectralHarmonicPair ell R) (c ζ : ℂ)
    (B B' : ℂ × ℂ →L[ℂ] ℂ × ℂ) (f : 𝓢(ℝ,ℂ)) (hfR : f R = 0)
    (he : spectralHarmonicPairComplexForm ell R w u₁ (spectralSecondTest ell R f) =
      inner ℂ (spectralLowerOrderOperator ell R hR
        (spectralRadialWeightMultiplier R w) (spectralRadialWeightMultiplier R a) c ζ B
        (spectralHarmonicObservation ell R hR u₁) +
        spectralLowerOrderSlope ell R hR (spectralRadialWeightMultiplier R w) B'
          (spectralHarmonicObservation ell R hR u₀)) (spectralSecondTest ell R f)) :
    (∫ r in (0 : ℝ)..R, star (deriv f r)*spectralSecondFlux ell R w a u₁ r) =
      -(∫ r in (0 : ℝ)..R, star (f r)*spectralSecondSource ell R w u₁ c ζ r) +
        (∫ r in (0 : ℝ)..R, (r : ℂ)^11 *
          (star (f r)*(w.density r • spectralHarmonicValue ell R u₀.fst r))) := by
  have h := spectralSecondFlux_pairing ell R hR w a u₁ c ζ f
  rw [spectralSecondTest_chain_balance ell R hR w a u₀ u₁ c ζ B B' f hfR he,
    spectral_radial_complex_integral R hR.le] at h
  linear_combination h

end DefocusingNLS

end OAI
