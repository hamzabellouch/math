import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.Probability.Moments.SubGaussian

namespace OAI

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

namespace Balanced
open scoped _root_.Balanced

theorem integral_mul_le_of_condExp_le
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    {F G : Ω → ℝ} {K : ℝ}
    (hFm : StronglyMeasurable[m] F) (hF : Integrable F μ)
    (hG : Integrable G μ) (hFG : Integrable (F * G) μ)
    (hFnonneg : ∀ᵐ ω ∂μ, 0 ≤ F ω)
    (hGcond : ∀ᵐ ω ∂μ, μ[G | m] ω ≤ K) :
    (∫ ω, F ω * G ω ∂μ) ≤ K * ∫ ω, F ω ∂μ := by
  have hpull := condExp_mul_of_stronglyMeasurable_left hFm hFG hG
  have hprod : Integrable (fun ω => F ω * μ[G | m] ω) μ :=
    integrable_condExp.congr hpull
  calc
    (∫ ω, F ω * G ω ∂μ) = ∫ ω, μ[F * G | m] ω ∂μ :=
      (integral_condExp hm).symm
    _ = ∫ ω, F ω * μ[G | m] ω ∂μ := integral_congr_ae hpull
    _ ≤ ∫ ω, F ω * K ∂μ := by
      apply integral_mono_ae hprod (hF.mul_const K)
      filter_upwards [hFnonneg, hGcond] with ω hFω hGω
      exact mul_le_mul_of_nonneg_left hGω hFω
    _ = K * ∫ ω, F ω ∂μ := by rw [integral_mul_const]; ring

theorem mgf_add_le_of_condExp_exp_le
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    {S Z : Ω → ℝ} {θ K : ℝ}
    (hSm : StronglyMeasurable[m] S)
    (hSexp : Integrable (fun ω => exp (θ * S ω)) μ)
    (hZexp : Integrable (fun ω => exp (θ * Z ω)) μ)
    (hSumexp : Integrable (fun ω => exp (θ * (S ω + Z ω))) μ)
    (hZcond : ∀ᵐ ω ∂μ, μ[fun ω => exp (θ * Z ω) | m] ω ≤ K) :
    mgf (S + Z) μ θ ≤ K * mgf S μ θ := by
  have hproduct : Integrable ((fun ω => exp (θ * S ω)) *
      (fun ω => exp (θ * Z ω))) μ := by
    convert hSumexp using 1
    ext ω
    simp only [Pi.mul_apply, mul_add, exp_add]
  simpa only [mgf, Pi.add_apply, mul_add, exp_add] using
    (integral_mul_le_of_condExp_le hm
      (Real.continuous_exp.comp_stronglyMeasurable (hSm.const_mul θ))
      hSexp hZexp hproduct
      (Filter.Eventually.of_forall fun ω => (exp_pos (θ * S ω)).le) hZcond)

end Balanced

end OAI
