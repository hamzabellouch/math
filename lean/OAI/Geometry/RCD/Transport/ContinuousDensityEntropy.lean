import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

namespace OAI

/-! # Nonnegative entropy of a normalized continuous density -/

open Filter MeasureTheory
open scoped ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

omit [CompactSpace X] [IsProbabilityMeasure μ] in
theorem continuous_density_integral (h : C(X,ℝ)) (h0 : ∀ x, 0 ≤ h x) (f : X → ℝ) :
    (∫ x, f x ∂μ.withDensity (fun x => ENNReal.ofReal (h x))) =
      ∫ x, h x*f x ∂μ := by
  rw [integral_withDensity_eq_integral_toReal_smul
    h.continuous.measurable.ennreal_ofReal (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (h0 _),smul_eq_mul]

theorem continuous_density_entropy_nonneg (h : C(X,ℝ)) (h0 : ∀ x, 0 < h x)
    [IsProbabilityMeasure (μ.withDensity (fun x => ENNReal.ofReal (h x)))] :
    0 ≤ ∫ x, Real.log (h x) ∂μ.withDensity (fun x => ENNReal.ofReal (h x)) := by
  have hi : Integrable h μ := h.continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have h1 : (∫ x, h x ∂μ)=1 := by
    have hh := continuous_density_integral μ h (fun x => (h0 x).le) (fun _ => 1)
    simpa using hh.symm
  have he := integral_mono_ae (hi.sub (integrable_const 1))
    ((Real.continuous_mul_log.comp h.continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))
    (Eventually.of_forall fun x => Real.self_sub_one_le_mul_log (h0 x).le)
  change (∫ x, h x-1 ∂μ) ≤ _ at he
  rw [integral_sub hi (integrable_const 1),h1] at he
  simp only [integral_const,probReal_univ,smul_eq_mul,one_mul,sub_self] at he
  rw [continuous_density_integral μ h (fun x => (h0 x).le)]
  exact he

end RegularPointCoordinates

end

end OAI
