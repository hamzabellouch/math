import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralL2ComplexMultiplier
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralHarmonicCoordinates

namespace OAI

/-! Exact scalar integrands of the completed weighted harmonic form. -/

open MeasureTheory
open scoped SchwartzMap
namespace DefocusingNLS

theorem spectralL2ComplexMultiplier_pairing (μ : Measure ℝ) (q : ℝ → ℝ)
    (hq : AEStronglyMeasurable q μ) (M : ℝ) (hb : ∀ᵐ r ∂μ, ‖q r‖ ≤ M)
    (u v : Lp ℂ 2 μ) :
    inner ℂ v (spectralL2ComplexMultiplier μ q hq M hb u)=
      ∫ r, star (v r)*(q r • u r) ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [spectralL2ComplexMultiplier_ae μ q hq M hb u] with r hr
  rw [RCLike.inner_apply',hr]
  rfl

theorem spectralL2ComplexMultiplier_pairing_test (μ : Measure ℝ) (q : ℝ → ℝ)
    (hq : AEStronglyMeasurable q μ) (M : ℝ) (hb : ∀ᵐ r ∂μ, ‖q r‖ ≤ M)
    (u v : Lp ℂ 2 μ) (f : ℝ → ℂ) (hv : v =ᵐ[μ] f) :
    inner ℂ v (spectralL2ComplexMultiplier μ q hq M hb u)=
      ∫ r, star (f r)*(q r • u r) ∂μ := by
  rw [spectralL2ComplexMultiplier_pairing]
  apply integral_congr_ae
  filter_upwards [hv] with r hr
  rw [hr]

theorem spectralHarmonicValue_smooth_ae (ell : ℕ) (R : ℝ) (f : 𝓢(ℝ,ℂ)) :
    spectralHarmonicValue ell R (spectralHarmonicSmoothEmbedding ell R f)
      =ᵐ[radialPressureMeasure R] f :=
  spectralRadialSmoothValue_ae R f

theorem spectralHarmonicDerivative_smooth_ae (ell : ℕ) (R : ℝ) (f : 𝓢(ℝ,ℂ)) :
    spectralHarmonicDerivative ell R (spectralHarmonicSmoothEmbedding ell R f)
      =ᵐ[radialPressureMeasure R] deriv f := by
  have h := spectralRadialSmoothValue_ae R (SchwartzMap.derivCLM ℂ ℂ f)
  change spectralRadialSmoothValue R (SchwartzMap.derivCLM ℂ ℂ f)
    =ᵐ[radialPressureMeasure R] deriv (f : ℝ → ℂ)
  filter_upwards [h] with r hr
  exact hr.trans (SchwartzMap.derivCLM_apply ℂ f r)

end DefocusingNLS

end OAI
