import OAI.Probability.SLE.Angle.AngleSpectralMoments

namespace OAI

/-! The explicitly positive spectral density defines a probability law
with the required polynomial moments. -/
noncomputable section
open Polynomial Set _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped ENNReal

namespace SLEExactGauge

def angleSpectralLaw (κ u θ : ℝ) : Measure ℝ :=
  (Target.angleLaw κ).withDensity (fun φ => ENNReal.ofReal (angleSpectralKernel κ u θ φ))

lemma angleSpectralKernel_integrable {κ u : ℝ} (hκ : 0<κ)
    (hu : angleSpectralMixingTime κ≤u) (θ : ℝ) :
    Integrable (angleSpectralKernel κ u θ) (Target.angleLaw κ) := by
  have : IsProbabilityMeasure (Target.angleLaw κ) := Target.angleLaw_isProbability hκ
  apply Integrable.of_bound (angleSpectralKernel_measurable hκ hu θ).aestronglyMeasurable 2
  apply Filter.Eventually.of_forall
  intro φ
  have hb := angleSpectralKernel_bounds hκ hu θ φ
  simpa only [Real.norm_eq_abs,abs_of_nonneg (by linarith : 0≤angleSpectralKernel κ u θ φ)] using hb.2

lemma angleSpectralKernel_mean {κ u : ℝ} (hκ : 0<κ)
    (hu : angleSpectralMixingTime κ≤u) (θ : ℝ) :
    (∫ φ, angleSpectralKernel κ u θ φ ∂Target.angleLaw κ)=1 := by
  simpa only [angleEigenPolynomial_zero,anglePolynomialTest,eval_one,mul_one,
    anglePolynomialEigenvalue,Nat.cast_zero,mul_zero,zero_pow (by decide : 2≠0),
    add_zero,neg_mul,Real.exp_zero] using angleSpectralKernel_pairing hκ hu θ 0

lemma angleSpectralLaw_isProbability {κ u : ℝ} (hκ : 0<κ)
    (hu : angleSpectralMixingTime κ≤u) (θ : ℝ) :
    IsProbabilityMeasure (angleSpectralLaw κ u θ) := by
  constructor
  rw [angleSpectralLaw,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (angleSpectralKernel_integrable hκ hu θ)
      (Filter.Eventually.of_forall (fun φ => by
        change (0:ℝ)≤angleSpectralKernel κ u θ φ
        have hb := (angleSpectralKernel_bounds hκ hu θ φ).1
        linarith)),angleSpectralKernel_mean hκ hu θ]
  exact ENNReal.ofReal_one

lemma angleSpectralLaw_integral {κ u : ℝ} (hκ : 0<κ)
    (hu : angleSpectralMixingTime κ≤u) (θ : ℝ) (f : ℝ → ℝ) :
    (∫ φ, f φ ∂angleSpectralLaw κ u θ)=
      ∫ φ, angleSpectralKernel κ u θ φ*f φ ∂Target.angleLaw κ := by
  rw [angleSpectralLaw,integral_withDensity_eq_integral_toReal_smul
    (angleSpectralKernel_measurable hκ hu θ).ennreal_ofReal
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro φ
  dsimp only
  rw [ENNReal.toReal_ofReal (by have hb := (angleSpectralKernel_bounds hκ hu θ φ).1; linarith)]
  rfl

lemma angleSpectralLaw_eigen_moment {κ u : ℝ} (hκ : 0<κ)
    (hu : angleSpectralMixingTime κ≤u) (θ : ℝ) (n : ℕ) :
    (∫ φ, anglePolynomialTest (angleEigenPolynomial κ n) φ ∂angleSpectralLaw κ u θ)=
      Real.exp (-u*anglePolynomialEigenvalue κ n)*anglePolynomialTest (angleEigenPolynomial κ n) θ := by
  rw [angleSpectralLaw_integral hκ hu θ]
  exact angleSpectralKernel_pairing hκ hu θ n

lemma angleSpectralLaw_ae_mem {κ u : ℝ} (θ : ℝ) :
    ∀ᵐ φ ∂angleSpectralLaw κ u θ, φ∈Ioo (0:ℝ) Real.pi :=
  (Target.angleLaw_ae_mem κ).filter_mono (withDensity_absolutelyContinuous _ _).ae_le

end SLEExactGauge

end

end OAI
