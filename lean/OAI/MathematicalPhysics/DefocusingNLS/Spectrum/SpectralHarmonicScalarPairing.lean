import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralWeightedPairing
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralHarmonicComplexForm

namespace OAI

/-! The scalar test identity of the weighted harmonic form, including its angular term. -/

open MeasureTheory
open scoped SchwartzMap
namespace DefocusingNLS

theorem spectral_star_inner {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (u v : E) : star (inner ℂ u v)=inner ℂ v u := by
  exact inner_conj_symm v u

theorem spectralHarmonicAngular_smooth_ae (ell : ℕ) (R : ℝ) (f : 𝓢(ℝ,ℂ)) :
    spectralHarmonicAngularValue ell R (spectralHarmonicSmoothEmbedding ell R f)
      =ᵐ[spectralAngularMeasure R]
        fun r => (Real.sqrt ((ell : ℝ)*(ell+10)) : ℂ)*f r := by
  rw [spectralHarmonicAngularValue_smooth]
  filter_upwards [Lp.coeFn_smul (Real.sqrt ((ell : ℝ)*(ell+10)) : ℂ)
      (spectralSmoothAngularValue R f),
    BoundedContinuousFunction.coeFn_toLp 2 (spectralAngularMeasure R) ℂ
      (SchwartzMap.toBoundedContinuousFunctionCLM ℂ ℝ ℂ f)] with r hs hf
  rw [hs,Pi.smul_apply]
  change spectralSmoothAngularValue R f r=f r at hf
  rw [hf]
  rfl

theorem spectralHarmonicScalar_pairing (ell : ℕ) (R : ℝ) (w : SpectralHarmonicWeight R)
    (u : SpectralHarmonicEnergy ell R) (f : 𝓢(ℝ,ℂ)) :
    star (spectralHarmonicComplexForm ell R w u (spectralHarmonicSmoothEmbedding ell R f))=
      (∫ r, star (f r)*(w.density r • spectralHarmonicValue ell R u r)
        ∂radialPressureMeasure R) +
      (∫ r, star (deriv f r)*(w.density r • spectralHarmonicDerivative ell R u r)
        ∂radialPressureMeasure R) +
      (((ell : ℝ)*(ell+10) : ℝ) : ℂ)*
        (∫ r, star (f r)*(w.density r • spectralHarmonicValue ell R u r)
          ∂spectralAngularMeasure R) := by
  let P := spectralL2ComplexMultiplier (radialPressureMeasure R) w.density
    w.radial_measurable w.bound w.radial_bound
  let A := spectralL2ComplexMultiplier (spectralAngularMeasure R) w.density
    w.angular_measurable w.bound w.angular_bound
  have hangle : inner ℂ
      (spectralHarmonicAngularValue ell R (spectralHarmonicSmoothEmbedding ell R f))
      (A (spectralHarmonicAngularValue ell R u))=
      (((ell : ℝ)*(ell+10) : ℝ) : ℂ)*
        (∫ r, star (f r)*(w.density r • spectralHarmonicValue ell R u r)
          ∂spectralAngularMeasure R) := by
    rw [spectralL2ComplexMultiplier_pairing,← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [spectralHarmonicAngular_smooth_ae ell R f,
      spectralHarmonicAngularValue_ae ell R u] with r hf hu
    rw [hf,hu]
    have hη : (Real.sqrt ((ell : ℝ)*(ell+10)) : ℂ)^2=
        (((ell : ℝ)*(ell+10) : ℝ) : ℂ) := by
      norm_cast
      exact Real.sq_sqrt (by positivity)
    simp only [Complex.real_smul,star_mul,Complex.star_def,Complex.conj_ofReal]
    calc
      _ = (Real.sqrt ((ell : ℝ)*(ell+10)) : ℂ)^2 *
          (star (f r)*(w.density r • spectralHarmonicValue ell R u r)) := by
        simp only [Complex.real_smul,Complex.star_def]
        ring
      _ = _ := by
        rw [hη]
        rfl
  change star (inner ℂ (P (spectralHarmonicValue ell R u))
      (spectralHarmonicValue ell R (spectralHarmonicSmoothEmbedding ell R f))+
    inner ℂ (P (spectralHarmonicDerivative ell R u))
      (spectralHarmonicDerivative ell R (spectralHarmonicSmoothEmbedding ell R f))+
    inner ℂ (A (spectralHarmonicAngularValue ell R u))
      (spectralHarmonicAngularValue ell R (spectralHarmonicSmoothEmbedding ell R f)))=_
  rw [star_add,star_add,spectral_star_inner,spectral_star_inner,spectral_star_inner,hangle]
  rw [spectralL2ComplexMultiplier_pairing_test _ _ _ _ _ _ _ _
    (spectralHarmonicValue_smooth_ae ell R f),
    spectralL2ComplexMultiplier_pairing_test _ _ _ _ _ _ _ _
    (spectralHarmonicDerivative_smooth_ae ell R f)]

end DefocusingNLS

end OAI
