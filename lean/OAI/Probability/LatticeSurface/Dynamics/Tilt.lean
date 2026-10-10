import Mathlib
import OAI.Probability.LatticeSurface.Dynamics.TiltSupport

namespace OAI

noncomputable section

namespace SmallTilts

open MeasureTheory Set

open scoped ENNReal NNReal

variable {Ω : Type*} [MeasurableSpace Ω]

def density (μ : Measure Ω) (Y : Ω → ℝ) (ω : Ω) : ENNReal :=
  (∫⁻ x,ENNReal.ofReal (Real.exp (Y x)) ∂μ)⁻¹ * ENNReal.ofReal (Real.exp (Y ω))

def tilted (μ : Measure Ω) (Y : Ω → ℝ) : Measure Ω := μ.withDensity (density μ Y)

end SmallTilts

namespace SmallTilts

open MeasureTheory Set

open scoped ENNReal NNReal

variable {Ω : Type*} [MeasurableSpace Ω]

lemma measurable_density (μ : Measure Ω) (Y : Ω → ℝ) (hY : Measurable Y) :
    Measurable (density μ Y) :=
  measurable_const.mul (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hY))

theorem small_linear_tilt (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Ω → ℝ) (hY : Measurable Y)
    (M : ℝ≥0) (hM : (∫⁻ ω,ENNReal.ofReal (Real.exp (2*|Y ω|)) ∂μ)≤M) :
    IsProbabilityMeasure (tilted μ Y) ∧
    (∫⁻ ω,(density μ Y ω)^2 ∂μ)≤(M:ENNReal)^3 ∧
    ∀ f : Ω → ENNReal,Measurable f →
      (∫⁻ ω,f ω ∂tilted μ Y)≤(M:ENNReal)^(3/2:ℝ)*(∫⁻ ω,(f ω)^2 ∂μ)^(1/2:ℝ) := by
  obtain ⟨hN0,hNt,hNi⟩ := normalizer_bounds μ Y hY M hM
  let N := ∫⁻ x,ENNReal.ofReal (Real.exp (Y x)) ∂μ
  have hd := measurable_density μ Y hY
  have hp : IsProbabilityMeasure (tilted μ Y) := by
    constructor
    rw [tilted,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
    simp only [density]
    rw [lintegral_const_mul _ (f := fun x => ENNReal.ofReal (Real.exp (Y x))) (by fun_prop)]
    exact ENNReal.inv_mul_cancel hN0 hNt
  have hsq : (∫⁻ ω,(density μ Y ω)^2 ∂μ)≤(M:ENNReal)^3 := by
    calc
      _ = N⁻¹^2 * (∫⁻ ω,ENNReal.ofReal (Real.exp (2*Y ω)) ∂μ) := by
        simp only [density,mul_pow,exp_square]
        exact lintegral_const_mul _ (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul hY)))
      _ ≤ (M:ENNReal)^2*(M:ENNReal) := by
        apply mul_le_mul'
        · exact pow_le_pow_left' hNi 2
        · exact (lintegral_mono (fun x => ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr
            (mul_le_mul_of_nonneg_left (le_abs_self (Y x)) (by norm_num))))).trans hM
      _ = _ := by ring
  refine ⟨hp,hsq,?_⟩
  intro f hf
  rw [tilted,lintegral_withDensity_eq_lintegral_mul μ hd hf]
  calc
    _ ≤ (∫⁻ x,(density μ Y x)^2 ∂μ)^(1/2:ℝ)*(∫⁻ x,(f x)^2 ∂μ)^(1/2:ℝ) := cauchy μ _ _ hd hf
    _ ≤ ((M:ENNReal)^3)^(1/2:ℝ)*(∫⁻ x,(f x)^2 ∂μ)^(1/2:ℝ) := by gcongr
    _ = _ := by rw [← ENNReal.rpow_natCast,← ENNReal.rpow_mul];norm_num

end SmallTilts

end

end OAI
