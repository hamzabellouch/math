import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralHarmonicScalarPairing

namespace OAI

/-! Integrability of the exact scalar test integrands. -/

open MeasureTheory
open scoped SchwartzMap
namespace DefocusingNLS

theorem spectralWeightedTest_integrable (μ : Measure ℝ) (q : ℝ → ℝ)
    (hq : AEStronglyMeasurable q μ) (M : ℝ) (hb : ∀ᵐ r ∂μ, ‖q r‖ ≤ M)
    (u v : Lp ℂ 2 μ) (f : ℝ → ℂ) (hv : v =ᵐ[μ] f) :
    Integrable (fun r => star (f r)*(q r • u r)) μ := by
  apply (L2.integrable_inner (𝕜 := ℂ) v
    (spectralL2ComplexMultiplier μ q hq M hb u)).congr
  filter_upwards [hv,spectralL2ComplexMultiplier_ae μ q hq M hb u] with r hr hp
  rw [RCLike.inner_apply',hr,hp]
  rfl

theorem spectralAngularTest_integrable (ell : ℕ) (R : ℝ) (w : SpectralHarmonicWeight R)
    (u : SpectralHarmonicEnergy ell R) (f : 𝓢(ℝ,ℂ)) :
    Integrable (fun r => (((ell : ℝ)*(ell+10) : ℝ) : ℂ)*
      (star (f r)*(w.density r • spectralHarmonicValue ell R u r)))
      (spectralAngularMeasure R) := by
  let A := spectralL2ComplexMultiplier (spectralAngularMeasure R) w.density
    w.angular_measurable w.bound w.angular_bound
  apply (L2.integrable_inner (𝕜 := ℂ)
    (spectralHarmonicAngularValue ell R (spectralHarmonicSmoothEmbedding ell R f))
    (A (spectralHarmonicAngularValue ell R u))).congr
  filter_upwards [spectralHarmonicAngular_smooth_ae ell R f,
    spectralHarmonicAngularValue_ae ell R u,
    spectralL2ComplexMultiplier_ae (spectralAngularMeasure R) w.density
      w.angular_measurable w.bound w.angular_bound (spectralHarmonicAngularValue ell R u)]
    with r hf hu hA
  rw [RCLike.inner_apply',hf,hA,hu]
  have hη : (Real.sqrt ((ell : ℝ)*(ell+10)) : ℂ)^2=
      (((ell : ℝ)*(ell+10) : ℝ) : ℂ) := by
    norm_cast
    exact Real.sq_sqrt (by positivity)
  rw [← hη]
  rw [map_mul,Complex.conj_ofReal]
  simp only [Complex.real_smul,Complex.star_def]
  ring

end DefocusingNLS

end OAI
