import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralBoundaryBalance
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralFirstFlux

namespace OAI

/-! Ordinary radial integration retains the boundary trace in the weak flux identity. -/

open MeasureTheory
open scoped SchwartzMap
namespace DefocusingNLS

theorem spectralSecondBoundaryBalance_to_flux (ell : ℕ) (R : ℝ) (hR : 0 < R)
    (w a : SpectralHarmonicWeight R) (u : SpectralHarmonicPair ell R) (c ζ : ℂ)
    (f : 𝓢(ℝ,ℂ)) (β : ℂ)
    (hbal :
      (∫ r, star (deriv f r)*(w.density r • spectralHarmonicDerivative ell R u.snd r)
        ∂radialPressureMeasure R) +
      (((ell : ℝ)*(ell+10) : ℝ) : ℂ)*
        (∫ r, star (f r)*(w.density r • spectralHarmonicValue ell R u.snd r)
          ∂spectralAngularMeasure R) +
      (c-ζ)*(∫ r, star (f r)*(w.density r • spectralHarmonicValue ell R u.fst r)
        ∂radialPressureMeasure R) +
      (∫ r, star (deriv f r)*(a.density r • spectralHarmonicValue ell R u.fst r)
        ∂radialPressureMeasure R)=β) :
    (∫ r in (0 : ℝ)..R, star (deriv f r)*spectralSecondFlux ell R w a u r)=
      β-(∫ r in (0 : ℝ)..R, star (f r)*spectralSecondSource ell R w u c ζ r) := by
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
    (∫ r, J₂ r ∂radialPressureMeasure R)=β at hbal
  rw [spectral_radial_complex_integral R hR.le,
    spectral_angular_complex_integral R hR.le,
    spectral_radial_complex_integral R hR.le,
    spectral_radial_complex_integral R hR.le] at hbal
  linear_combination hbal

theorem spectralSecond_boundaryFlux (ell : ℕ) (R : ℝ) (hR : 0 < R)
    (w a : SpectralHarmonicWeight R) (u : SpectralHarmonicPair ell R) (c ζ : ℂ)
    (B : ℂ × ℂ →L[ℂ] ℂ × ℂ) (f : 𝓢(ℝ,ℂ))
    (he : spectralHarmonicPairComplexForm ell R w u (spectralSecondTest ell R f)=
      inner ℂ (spectralLowerOrderOperator ell R hR
        (spectralRadialWeightMultiplier R w) (spectralRadialWeightMultiplier R a) c ζ B
        (spectralHarmonicObservation ell R hR u)) (spectralSecondTest ell R f)) :
    (∫ r in (0 : ℝ)..R, star (deriv f r)*spectralSecondFlux ell R w a u r)=
      star (f R)*(B (spectralHarmonicPairTraces ell R hR u)).2-
        (∫ r in (0 : ℝ)..R, star (f r)*spectralSecondSource ell R w u c ζ r) :=
  spectralSecondBoundaryBalance_to_flux ell R hR w a u c ζ f _
    (spectralSecondTest_boundaryBalance ell R hR w a u c ζ B f he)

theorem spectralFirstBoundaryBalance_to_flux (ell : ℕ) (R : ℝ) (hR : 0 < R)
    (w a : SpectralHarmonicWeight R) (u : SpectralHarmonicPair ell R) (c ζ : ℂ)
    (B : ℂ × ℂ →L[ℂ] ℂ × ℂ) (f : 𝓢(ℝ,ℂ))
    (he : spectralHarmonicPairComplexForm ell R w u (spectralFirstTest ell R f)=
      inner ℂ (spectralLowerOrderOperator ell R hR
        (spectralRadialWeightMultiplier R w) (spectralRadialWeightMultiplier R a) c ζ B
        (spectralHarmonicObservation ell R hR u)) (spectralFirstTest ell R f)) :
    (∫ r in (0 : ℝ)..R, star (deriv f r)*
      spectralSecondFlux ell R w (spectralNegWeight a) (spectralSwapPair ell R u) r)=
      star (f R)*(B (spectralHarmonicPairTraces ell R hR u)).1-
        (∫ r in (0 : ℝ)..R, star (f r)*
        spectralSecondSource ell R w (spectralSwapPair ell R u) (-c) (-ζ) r) := by
  have hb := spectralFirstTest_boundaryBalance ell R hR w a u c ζ B f he
  apply spectralSecondBoundaryBalance_to_flux ell R hR w (spectralNegWeight a)
    (spectralSwapPair ell R u) (-c) (-ζ) f
    (star (f R)*(B (spectralHarmonicPairTraces ell R hR u)).1)
  change (∫ r, star (deriv f r)*(w.density r • spectralHarmonicDerivative ell R u.fst r)
      ∂radialPressureMeasure R) +
    (((ell : ℝ)*(ell+10) : ℝ) : ℂ)*
      (∫ r, star (f r)*(w.density r • spectralHarmonicValue ell R u.fst r)
        ∂spectralAngularMeasure R) +
    (-c- -ζ)*(∫ r, star (f r)*(w.density r • spectralHarmonicValue ell R u.snd r)
      ∂radialPressureMeasure R) +
    (∫ r, star (deriv f r)*(-a.density r • spectralHarmonicValue ell R u.snd r)
      ∂radialPressureMeasure R)=star (f R)*(B (spectralHarmonicPairTraces ell R hR u)).1
  simp only [neg_smul,mul_neg,integral_neg]
  linear_combination hb

end DefocusingNLS

end OAI
