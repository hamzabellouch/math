import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralSecondBalance
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralWeightedTestIntegrable
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralMeasureIntegrability

namespace OAI

/-! The scalar balance is the ordinary weak derivative equation for the weighted flux. -/

open MeasureTheory
open scoped SchwartzMap
namespace DefocusingNLS

noncomputable def spectralSecondFlux (ell : ℕ) (R : ℝ) (w a : SpectralHarmonicWeight R)
    (u : SpectralHarmonicPair ell R) (r : ℝ) : ℂ :=
  (r : ℂ)^11*(w.density r • spectralHarmonicDerivative ell R u.snd r +
    a.density r • spectralHarmonicValue ell R u.fst r)

noncomputable def spectralSecondSource (ell : ℕ) (R : ℝ) (w : SpectralHarmonicWeight R)
    (u : SpectralHarmonicPair ell R) (c ζ : ℂ) (r : ℝ) : ℂ :=
  (((ell : ℝ)*(ell+10) : ℝ) : ℂ)*(r : ℂ)^9*
    (w.density r • spectralHarmonicValue ell R u.snd r) +
  (c-ζ)*(r : ℂ)^11*(w.density r • spectralHarmonicValue ell R u.fst r)

theorem spectralSecondBalance_to_flux (ell : ℕ) (R : ℝ) (hR : 0 < R)
    (w a : SpectralHarmonicWeight R) (u : SpectralHarmonicPair ell R) (c ζ : ℂ)
    (f : 𝓢(ℝ,ℂ))
    (hbal :
      (∫ r, star (deriv f r)*(w.density r • spectralHarmonicDerivative ell R u.snd r)
        ∂radialPressureMeasure R) +
      (((ell : ℝ)*(ell+10) : ℝ) : ℂ)*
        (∫ r, star (f r)*(w.density r • spectralHarmonicValue ell R u.snd r)
          ∂spectralAngularMeasure R) +
      (c-ζ)*(∫ r, star (f r)*(w.density r • spectralHarmonicValue ell R u.fst r)
        ∂radialPressureMeasure R) +
      (∫ r, star (deriv f r)*(a.density r • spectralHarmonicValue ell R u.fst r)
        ∂radialPressureMeasure R)=0) :
    (∫ r in (0 : ℝ)..R, star (deriv f r)*spectralSecondFlux ell R w a u r)=
      -(∫ r in (0 : ℝ)..R, star (f r)*spectralSecondSource ell R w u c ζ r) := by
  let J₁ := fun r => star (deriv f r)*(w.density r • spectralHarmonicDerivative ell R u.snd r)
  let J₂ := fun r => star (deriv f r)*(a.density r • spectralHarmonicValue ell R u.fst r)
  let J₃ := fun r => star (f r)*(w.density r • spectralHarmonicValue ell R u.snd r)
  let J₄ := fun r => star (f r)*(w.density r • spectralHarmonicValue ell R u.fst r)
  let η : ℂ := (((ell : ℝ)*(ell+10) : ℝ) : ℂ)
  have hd (v : SpectralRadialL2 R) (b : SpectralHarmonicWeight R) :
      Integrable (fun r => star (deriv f r)*(b.density r • v r)) (radialPressureMeasure R) :=
    spectralWeightedTest_integrable _ _ b.radial_measurable b.bound b.radial_bound v
      (spectralHarmonicDerivative ell R (spectralHarmonicSmoothEmbedding ell R f))
      (deriv f) (spectralHarmonicDerivative_smooth_ae ell R f)
  have hv (v : SpectralRadialL2 R) :
      Integrable (fun r => star (f r)*(w.density r • v r)) (radialPressureMeasure R) :=
    spectralWeightedTest_integrable _ _ w.radial_measurable w.bound w.radial_bound v
      (spectralHarmonicValue ell R (spectralHarmonicSmoothEmbedding ell R f))
      f (spectralHarmonicValue_smooth_ae ell R f)
  have hi₁ : IntervalIntegrable (fun r => (r : ℂ)^11*J₁ r) volume 0 R :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hR.le).mpr
      (spectralRadial_integrableOn R J₁ (hd _ w))
  have hi₂ : IntervalIntegrable (fun r => (r : ℂ)^11*J₂ r) volume 0 R :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hR.le).mpr
      (spectralRadial_integrableOn R J₂ (hd _ a))
  have hi₄ : IntervalIntegrable (fun r => (r : ℂ)^11*J₄ r) volume 0 R :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hR.le).mpr
      (spectralRadial_integrableOn R J₄ (hv _))
  have hi₃ : IntervalIntegrable (fun r => η*((r : ℂ)^9*J₃ r)) volume 0 R := by
    have hi := (intervalIntegrable_iff_integrableOn_Icc_of_le hR.le).mpr
      (spectralAngular_integrableOn R _ (spectralAngularTest_integrable ell R w u.snd f))
    convert hi using 1
    funext r
    dsimp only [η,J₃]
    ring
  have hflux : (∫ r in (0 : ℝ)..R, star (deriv f r)*spectralSecondFlux ell R w a u r)=
      (∫ r in (0 : ℝ)..R, (r : ℂ)^11*J₁ r)+
        ∫ r in (0 : ℝ)..R, (r : ℂ)^11*J₂ r := by
    rw [← intervalIntegral.integral_add hi₁ hi₂]
    apply intervalIntegral.integral_congr
    intro r _
    dsimp only [spectralSecondFlux,J₁,J₂]
    ring
  have hsource : (∫ r in (0 : ℝ)..R, star (f r)*spectralSecondSource ell R w u c ζ r)=
      η*(∫ r in (0 : ℝ)..R, (r : ℂ)^9*J₃ r)+
        (c-ζ)*(∫ r in (0 : ℝ)..R, (r : ℂ)^11*J₄ r) := by
    rw [← intervalIntegral.integral_const_mul,← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add hi₃ (hi₄.const_mul (c-ζ))]
    apply intervalIntegral.integral_congr
    intro r _
    dsimp only [spectralSecondSource,J₃,J₄,η]
    ring
  rw [hflux,hsource]
  change (∫ r, J₁ r ∂radialPressureMeasure R)+
    η*(∫ r, J₃ r ∂spectralAngularMeasure R)+
    (c-ζ)*(∫ r, J₄ r ∂radialPressureMeasure R)+
    (∫ r, J₂ r ∂radialPressureMeasure R)=0 at hbal
  rw [spectral_radial_complex_integral R hR.le,
    spectral_angular_complex_integral R hR.le,
    spectral_radial_complex_integral R hR.le,
    spectral_radial_complex_integral R hR.le] at hbal
  linear_combination hbal

end DefocusingNLS

end OAI
