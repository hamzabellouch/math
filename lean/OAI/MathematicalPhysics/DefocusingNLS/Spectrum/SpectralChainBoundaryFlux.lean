import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralChainBoundaryBalance
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralChainSourceIntegral

namespace OAI

/-! Exact outer-boundary identity for both inhomogeneous chain fluxes. -/

open MeasureTheory
open scoped SchwartzMap
namespace DefocusingNLS

theorem spectralSecondChain_boundary_flux (ell : ℕ) (R : ℝ) (hR : 0 < R)
    (w a : SpectralHarmonicWeight R) (u₀ u₁ : SpectralHarmonicPair ell R) (c ζ : ℂ)
    (B B' : ℂ × ℂ →L[ℂ] ℂ × ℂ) (f : 𝓢(ℝ,ℂ))
    (he : spectralHarmonicPairComplexForm ell R w u₁ (spectralSecondTest ell R f) =
      inner ℂ (spectralLowerOrderOperator ell R hR
        (spectralRadialWeightMultiplier R w) (spectralRadialWeightMultiplier R a) c ζ B
        (spectralHarmonicObservation ell R hR u₁) +
        spectralLowerOrderSlope ell R hR (spectralRadialWeightMultiplier R w) B'
          (spectralHarmonicObservation ell R hR u₀)) (spectralSecondTest ell R f)) :
    (∫ r in (0 : ℝ)..R, star (deriv f r)*spectralSecondFlux ell R w a u₁ r) =
      star (f R) * ((B (spectralHarmonicPairTraces ell R hR u₁)).2 +
        (B' (spectralHarmonicPairTraces ell R hR u₀)).2) -
        (∫ r in (0 : ℝ)..R, star (f r)*spectralSecondChainSource ell R hR w u₀ u₁ c ζ r) := by
  have h := spectralSecondFlux_pairing ell R hR w a u₁ c ζ f
  rw [spectralSecondTest_chain_boundaryBalance ell R hR w a u₀ u₁ c ζ B B' f he,
    spectral_radial_complex_integral R hR.le] at h
  rw [spectralSecondChainSource_integral ell R hR w u₀ u₁ c ζ f]
  linear_combination h

theorem spectralFirstChain_boundary_flux (ell : ℕ) (R : ℝ) (hR : 0 < R)
    (w a : SpectralHarmonicWeight R) (u₀ u₁ : SpectralHarmonicPair ell R) (c ζ : ℂ)
    (B B' : ℂ × ℂ →L[ℂ] ℂ × ℂ) (f : 𝓢(ℝ,ℂ))
    (he : spectralHarmonicPairComplexForm ell R w u₁ (spectralFirstTest ell R f) =
      inner ℂ (spectralLowerOrderOperator ell R hR
        (spectralRadialWeightMultiplier R w) (spectralRadialWeightMultiplier R a) c ζ B
        (spectralHarmonicObservation ell R hR u₁) +
        spectralLowerOrderSlope ell R hR (spectralRadialWeightMultiplier R w) B'
          (spectralHarmonicObservation ell R hR u₀)) (spectralFirstTest ell R f)) :
    (∫ r in (0 : ℝ)..R, star (deriv f r)*
      spectralSecondFlux ell R w (spectralNegWeight a) (spectralSwapPair ell R u₁) r) =
      star (f R) * ((B (spectralHarmonicPairTraces ell R hR u₁)).1 +
        (B' (spectralHarmonicPairTraces ell R hR u₀)).1) -
        (∫ r in (0 : ℝ)..R, star (f r)*spectralFirstChainSource ell R hR w u₀ u₁ c ζ r) := by
  have hb := spectralFirstTest_chain_boundaryBalance ell R hR w a u₀ u₁ c ζ B B' f he
  have h := spectralSecondFlux_pairing ell R hR w (spectralNegWeight a)
    (spectralSwapPair ell R u₁) (-c) (-ζ) f
  change _ = (∫ r, star (deriv f r)*(w.density r • spectralHarmonicDerivative ell R u₁.fst r)
      ∂radialPressureMeasure R) +
    (((ell : ℝ)*(ell+10) : ℝ) : ℂ)*
      (∫ r, star (f r)*(w.density r • spectralHarmonicValue ell R u₁.fst r)
        ∂spectralAngularMeasure R) +
    (-c- -ζ)*(∫ r, star (f r)*(w.density r • spectralHarmonicValue ell R u₁.snd r)
      ∂radialPressureMeasure R) +
    (∫ r, star (deriv f r)*(-a.density r • spectralHarmonicValue ell R u₁.snd r)
      ∂radialPressureMeasure R) at h
  have hneg : -c- -ζ = -(c-ζ) := by ring
  simp only [hneg, neg_smul, mul_neg, neg_mul, integral_neg] at h
  rw [show ∀ x y z t : ℂ, x+y+-z+-t=x+y-z-t by intros; ring] at h
  rw [hb, spectral_radial_complex_integral R hR.le] at h
  rw [spectralFirstChainSource_integral ell R hR w u₀ u₁ c ζ f]
  linear_combination h

end DefocusingNLS

end OAI
