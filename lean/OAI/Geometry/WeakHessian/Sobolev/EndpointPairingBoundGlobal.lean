import Mathlib
import OAI.Geometry.WeakHessian.Transport.MapEvalReal
import OAI.Geometry.WeakHessian.Sobolev.AeEndpointGlobal

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped NNReal
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open scoped Topology
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace

namespace WeakHessian
open MeasureTheory
open scoped Topology InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [Nonempty X]
  {m : Measure X}

lemma IsLocalWeakUpperGradient.endpoint_pairing_bound_global
    {f D : Lp ℝ 2 m} (hf : IsLocalWeakUpperGradient m (f : X → ℝ) (D : X → ℝ))
    {π : Measure (Curve X)} (hπ : IsTestPlan m π)
    {C : ℝ≥0} (hC : ∀ t : Time, π.map (fun γ => γ t) ≤ (C:ℝ≥0∞) • m)
    {A : ℝ} (hA : 0 ≤ A)
    (ha : (∫⁻ γ, ∫⁻ r in Icc (0:ℝ) 1, (metricSpeed γ r)^2 ∂volume ∂π) ≤ ENNReal.ofReal A) :
    |(∫ x, f x ∂(π.map (fun γ => γ timeOne))) -
      (∫ x, f x ∂(π.map (fun γ => γ timeZero)))| ≤ Real.sqrt C * ‖D‖ * Real.sqrt A := by
  let : IsProbabilityMeasure π := hπ.1
  have hm (r : Time) : MemLp (f : X → ℝ) 2 (π.map (fun γ => γ r)) :=
    ((Lp.memLp f).smul_measure ENNReal.coe_ne_top).mono_measure (hC r)
  have hi (r : Time) : Integrable (fun γ : Curve X => f (γ r)) π :=
    ((hm r).comp_of_map (continuous_eval_const r).measurable.aemeasurable).integrable (by norm_num)
  have hweak := hf.integrated_global (Lp.aestronglyMeasurable f).aemeasurable hπ
  have haction := hπ.lintegral_abs_action_le hC (Lp.aestronglyMeasurable D)
  have hdpos : (∫⁻ γ, ∫⁻ r in Icc (0:ℝ) 1,
      ENNReal.ofReal (D (evalReal γ r)) * metricSpeed γ r ∂volume ∂π) ≤
      ∫⁻ γ, ∫⁻ r in Icc (0:ℝ) 1,
      ENNReal.ofReal |D (evalReal γ r)| * metricSpeed γ r ∂volume ∂π := by
    apply lintegral_mono
    intro γ
    apply lintegral_mono
    intro r
    exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (le_abs_self _)) _
  have hb : ENNReal.ofReal |∫ γ, f (γ timeOne)-f (γ timeZero) ∂π| ≤
      ((C:ℝ≥0∞)^(1/(2:ℝ))*eLpNorm (D : X → ℝ) 2 m) * (ENNReal.ofReal A)^(1/(2:ℝ)) := by
    have H := enorm_integral_le_lintegral_enorm (μ := π) (fun γ : Curve X => f (γ timeOne)-f (γ timeZero))
    simp only [Real.enorm_eq_ofReal_abs] at H
    exact (H.trans (hweak.trans (hdpos.trans haction))).trans
      (by gcongr)
  rw [← Lp.enorm_def] at hb
  have hreal := ENNReal.toReal_mono (by finiteness) hb
  rw [ENNReal.toReal_ofReal (abs_nonneg _), ENNReal.toReal_mul, ENNReal.toReal_mul,
    ← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow, ENNReal.coe_toReal,
    ENNReal.toReal_ofReal hA, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hreal
  rw [integral_sub (hi timeOne) (hi timeZero)] at hreal
  rw [integral_map (continuous_eval_const timeOne).measurable.aemeasurable
      (hm timeOne).aestronglyMeasurable,
    integral_map (continuous_eval_const timeZero).measurable.aemeasurable
      (hm timeZero).aestronglyMeasurable]
  simpa only [toReal_enorm] using hreal

end WeakHessian

end
end InlinedFile0

end OAI
