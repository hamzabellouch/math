import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralFirstBalance
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralSecondFluxRegularity

namespace OAI

/-! The first channel has flux r¹¹(μ f′−A g), with tests confined outside the core. -/

open MeasureTheory
open scoped SchwartzMap
namespace DefocusingNLS

noncomputable def spectralNegWeight {R : ℝ} (a : SpectralHarmonicWeight R) :
    SpectralHarmonicWeight R where
  density := fun r => -a.density r
  bound := a.bound
  radial_measurable := a.radial_measurable.neg
  angular_measurable := a.angular_measurable.neg
  radial_bound := by simpa only [norm_neg] using a.radial_bound
  angular_bound := by simpa only [norm_neg] using a.angular_bound

noncomputable def spectralSwapPair (ell : ℕ) (R : ℝ) (u : SpectralHarmonicPair ell R) :
    SpectralHarmonicPair ell R :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ (SpectralHarmonicEnergy ell R)
    (SpectralHarmonicEnergy ell R)).symm (u.snd,u.fst)

theorem spectralFirstBalance_to_flux (ell : ℕ) (R : ℝ) (hR : 0 < R)
    (w a : SpectralHarmonicWeight R) (u : SpectralHarmonicPair ell R) (c ζ : ℂ)
    (B : ℂ × ℂ →L[ℂ] ℂ × ℂ) (f : 𝓢(ℝ,ℂ)) (hfR : f R=0)
    (he : spectralHarmonicPairComplexForm ell R w u (spectralFirstTest ell R f)=
      inner ℂ (spectralLowerOrderOperator ell R hR
        (spectralRadialWeightMultiplier R w) (spectralRadialWeightMultiplier R a) c ζ B
        (spectralHarmonicObservation ell R hR u)) (spectralFirstTest ell R f)) :
    (∫ r in (0 : ℝ)..R, star (deriv f r)*
      spectralSecondFlux ell R w (spectralNegWeight a) (spectralSwapPair ell R u) r)=
      -(∫ r in (0 : ℝ)..R, star (f r)*
        spectralSecondSource ell R w (spectralSwapPair ell R u) (-c) (-ζ) r) := by
  have hb := spectralFirstTest_balance ell R hR w a u c ζ B f hfR he
  apply spectralSecondBalance_to_flux ell R hR w (spectralNegWeight a)
    (spectralSwapPair ell R u) (-c) (-ζ) f
  change (∫ r, star (deriv f r)*(w.density r • spectralHarmonicDerivative ell R u.fst r)
      ∂radialPressureMeasure R) +
    (((ell : ℝ)*(ell+10) : ℝ) : ℂ)*
      (∫ r, star (f r)*(w.density r • spectralHarmonicValue ell R u.fst r)
        ∂spectralAngularMeasure R) +
    (-c- -ζ)*(∫ r, star (f r)*(w.density r • spectralHarmonicValue ell R u.snd r)
      ∂radialPressureMeasure R) +
    (∫ r, star (deriv f r)*(-a.density r • spectralHarmonicValue ell R u.snd r)
      ∂radialPressureMeasure R)=0
  simp only [neg_smul,mul_neg,integral_neg]
  linear_combination hb

end DefocusingNLS

end OAI
