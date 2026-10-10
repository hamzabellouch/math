import OAI.Analysis.IrrationalRotation.Spectral.ScalarDeterminantZero
import OAI.Analysis.IrrationalRotation.Rotation.AnalyticWeightBridge
import OAI.Analysis.IrrationalRotation.Spectral.SpectralNaturality

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace Invariant233

theorem ScalarDeterminant.regularized_determinant_eq_zero_of_log_integral
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
    {f : X → ℝ} (hm : Measurable f) (hbound : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
    (hpos : ∀ᵐ x ∂μ, 0 < f x) (hinf : HasNegInfiniteLogIntegral μ f) :
    (⨅ ε : {r : ℝ // 0 < r}, ENNReal.ofReal
      (Real.exp ((∫ x, Real.log (f x ^ 2 + ε.val) ∂μ) / 2))) = 0 := by
  apply ScalarDeterminant.regularized_determinant_eq_zero hm hbound
  intro B
  obtain ⟨M, hM, hlt⟩ := exists_pos_truncated_log_integral_lt f hm
    (fun x => (hbound x).1) (fun x => (hbound x).2) hpos
    ((hasNegInfiniteLogIntegral_iff_of_ae_pos f hpos).mp hinf) (-B / 2)
  refine ⟨M, hM, ?_⟩
  linarith

theorem IsContinuousCircleWeight.regularized_determinant_eq_zero
    {f : Circle → ℝ} (hf : IsContinuousCircleWeight f) :
    (⨅ ε : {r : ℝ // 0 < r}, ENNReal.ofReal
      (Real.exp ((∫ x, Real.log (f x ^ 2 + ε.val) ∂circleMeasure) / 2))) = 0 := by
  let : IsProbabilityMeasure circleMeasure := ⟨by
    simp only [circleMeasure, AddCircle.measure_univ, ENNReal.ofReal_one]⟩
  exact ScalarDeterminant.regularized_determinant_eq_zero_of_log_integral
    hf.1.measurable hf.2.1 hf.ae_pos hf.2.2.2

variable {A : Type*} [CStarAlgebra A]

theorem fugledeKadisonDeterminant_continuous_circle_weight
    (π : C(Circle, ℂ) →⋆ₐ[ℂ] A) (τ : TracialState A)
    (hτ : ∀ g : C(Circle, ℂ), τ (π g) = ∫ x, g x ∂circleMeasure)
    (f : C(Circle, ℂ)) (hf : IsContinuousCircleWeight (fun x => ‖f x‖)) :
    fugledeKadisonDeterminant τ (π f) = 0 := by
  rw [fugledeKadisonDeterminant_continuous_representation circleMeasure π τ hτ]
  exact hf.regularized_determinant_eq_zero

theorem fugledeKadisonDeterminant_real_circle_weight
    (π : C(Circle, ℂ) →⋆ₐ[ℂ] A) (τ : TracialState A)
    (hτ : ∀ g : C(Circle, ℂ), τ (π g) = ∫ x, g x ∂circleMeasure)
    (f : C(Circle, ℝ)) (hf : IsContinuousCircleWeight f) :
    fugledeKadisonDeterminant τ
      (π ⟨fun x => (f x : ℂ), Complex.continuous_ofReal.comp f.continuous⟩) = 0 := by
  apply fugledeKadisonDeterminant_continuous_circle_weight π τ hτ
  convert hf using 1
  funext x
  simp only [ContinuousMap.coe_mk, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (hf.2.1 x).1]

theorem fugledeKadisonDeterminant_unitary_real_circle_weight
    (π : C(Circle, ℂ) →⋆ₐ[ℂ] A) (τ : TracialState A)
    (hτ : ∀ g : C(Circle, ℂ), τ (π g) = ∫ x, g x ∂circleMeasure)
    (u : unitary A) (f : C(Circle, ℝ)) (hf : IsContinuousCircleWeight f) :
    fugledeKadisonDeterminant τ
      ((u : A) * π ⟨fun x => (f x : ℂ), Complex.continuous_ofReal.comp f.continuous⟩) = 0 := by
  rw [fugledeKadisonDeterminant_unitary_mul]
  exact fugledeKadisonDeterminant_real_circle_weight π τ hτ f hf

end Invariant233

end

end OAI
