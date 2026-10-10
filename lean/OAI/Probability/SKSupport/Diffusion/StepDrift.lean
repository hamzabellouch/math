import Mathlib
import OAI.Probability.SKSupport.Moments.IntegratedCompletionSquare

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK.WeakIto
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

def stepDrift (α : ℝ → Ω → ℝ) (s h c : ℝ) (ω : Ω) : ℝ :=
  ∫ r in s..s+h, c*α r ω

def stepCost (α : ℝ → Ω → ℝ) (s h c : ℝ) (ω : Ω) : ℝ :=
  (1/2:ℝ)*∫ r in s..s+h, c*(α r ω)^2

lemma bounded_control_intervalIntegrable {α : ℝ → Ω → ℝ}
    (hm : Measurable (fun p : ℝ × Ω => α p.1 p.2))
    (hb : ∀ r ω, |α r ω| ≤ 1) (s h : ℝ) (hh : 0 ≤ h) (ω : Ω) :
    IntervalIntegrable (fun r => α r ω) volume s (s+h) ∧
    IntervalIntegrable (fun r => (α r ω)^2) volume s (s+h) := by
  have hm₁ : Measurable (fun r => α r ω) := hm.comp measurable_prodMk_right
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith : s ≤ s+h),
    intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith : s ≤ s+h)]
  constructor
  · exact Integrable.of_bound hm₁.aestronglyMeasurable 1
      (Filter.Eventually.of_forall (fun r => by simpa only [Real.norm_eq_abs] using hb r ω))
  · apply Integrable.of_bound (hm₁.pow_const 2).aestronglyMeasurable 1
    filter_upwards [] with r
    rw [Real.norm_eq_abs, abs_pow]
    simpa using pow_le_pow_left₀ (abs_nonneg (α r ω)) (hb r ω) 2

lemma stepDrift_measurable {α : ℝ → Ω → ℝ}
    (hm : Measurable (fun p : ℝ × Ω => α p.1 p.2)) (s h c : ℝ) (hh : 0 ≤ h) :
    Measurable (stepDrift α s h c) := by
  unfold stepDrift
  simp_rw [intervalIntegral.integral_of_le (by linarith : s ≤ s+h)]
  exact (hm.const_mul c).stronglyMeasurable.integral_prod_left.measurable

lemma stepCost_measurable {α : ℝ → Ω → ℝ}
    (hm : Measurable (fun p : ℝ × Ω => α p.1 p.2)) (s h c : ℝ) (hh : 0 ≤ h) :
    Measurable (stepCost α s h c) := by
  unfold stepCost
  simp_rw [intervalIntegral.integral_of_le (by linarith : s ≤ s+h)]
  exact (((hm.pow_const 2).const_mul c).stronglyMeasurable.integral_prod_left.measurable).const_mul _

omit [MeasurableSpace Ω] in
lemma stepDrift_bound {α : ℝ → Ω → ℝ}
    (hb : ∀ r ω, |α r ω| ≤ 1) (s h c : ℝ) (hh : 0 ≤ h) (hc : 0 ≤ c) (ω : Ω) :
    |stepDrift α s h c ω| ≤ c*h := by
  unfold stepDrift
  rw [← Real.norm_eq_abs]
  have hbound : ‖∫ r in s..s+h, c*α r ω‖ ≤ ∫ _r in s..s+h, c := by
    apply intervalIntegral.norm_integral_le_of_norm_le (by linarith)
      _ intervalIntegrable_const
    filter_upwards [] with r hr
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hc]
    nlinarith [hb r ω]
  simpa only [intervalIntegral.integral_const, smul_eq_mul, add_sub_cancel_left, mul_comm] using hbound

omit [MeasurableSpace Ω] in
lemma stepCost_bound {α : ℝ → Ω → ℝ}
    (hb : ∀ r ω, |α r ω| ≤ 1) (s h c : ℝ) (hh : 0 ≤ h) (hc : 0 ≤ c) (ω : Ω) :
    |stepCost α s h c ω| ≤ c*h/2 := by
  unfold stepCost
  rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)]
  have hbound : |∫ r in s..s+h, c*(α r ω)^2| ≤ c*h := by
    apply stepDrift_bound (α := fun r ω => (α r ω)^2) _ s h c hh hc ω
    intro r ω
    rw [abs_pow]
    simpa using pow_le_pow_left₀ (abs_nonneg (α r ω)) (hb r ω) 2
  linarith

lemma stepDrift_integrable {α : ℝ → Ω → ℝ}
    (hm : Measurable (fun p : ℝ × Ω => α p.1 p.2))
    (hb : ∀ r ω, |α r ω| ≤ 1) (s h c : ℝ) (hh : 0 ≤ h) (hc : 0 ≤ c) :
    Integrable (stepDrift α s h c) P := by
  exact Integrable.of_bound (stepDrift_measurable hm s h c hh).aestronglyMeasurable (c*h)
    (Filter.Eventually.of_forall (fun ω => by
      simpa only [Real.norm_eq_abs] using (stepDrift_bound hb s h c hh hc ω)))

lemma stepCost_integrable {α : ℝ → Ω → ℝ}
    (hm : Measurable (fun p : ℝ × Ω => α p.1 p.2))
    (hb : ∀ r ω, |α r ω| ≤ 1) (s h c : ℝ) (hh : 0 ≤ h) (hc : 0 ≤ c) :
    Integrable (stepCost α s h c) P := by
  exact Integrable.of_bound (stepCost_measurable hm s h c hh).aestronglyMeasurable (c*h/2)
    (Filter.Eventually.of_forall (fun ω => by
      simpa only [Real.norm_eq_abs] using (stepCost_bound hb s h c hh hc ω)))

lemma step_completion_square {α : ℝ → Ω → ℝ}
    (hm : Measurable (fun p : ℝ × Ω => α p.1 p.2))
    (hb : ∀ r ω, |α r ω| ≤ 1) (s h c : ℝ) (hh : 0 ≤ h) (hc : 0 ≤ c)
    (u : ℝ) (ω : Ω) :
    u*stepDrift α s h c ω-stepCost α s h c ω ≤ h*c/2*u^2 := by
  obtain ⟨hα,hα₂⟩ := bounded_control_intervalIntegrable hm hb s h hh ω
  simpa only [stepDrift, stepCost, add_sub_cancel_left] using
    integrated_completion_square s (s+h) c u (by linarith) hc hα hα₂

end ZeroTemperatureSK.WeakIto

end
end
end

end OAI
