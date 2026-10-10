import Mathlib
import OAI.Probability.SKSupport.Foundations.Control

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK

variable {Ω : Type*} [MeasurableSpace Ω]

@[simp] lemma OrderParameter.abs_extend (γ : OrderParameter) (s : ℝ) :
    |extend γ.val s| = extend γ.val s := abs_of_nonneg (γ.extend_nonneg s)

lemma Control.measurable_drift_integral {W : BrownianSystem Ω} (γ : OrderParameter)
    (t : ℝ) (ht : t ≤ 1) (α : Control W (Real.toNNReal t)) :
    Measurable (fun ω => ∫ s in t..1, extend γ.val s * α.val (Real.toNNReal (s - t)) ω) := by
  simp_rw [intervalIntegral.integral_of_le ht]
  exact ((γ.measurable_extend.comp measurable_fst).mul
    (α.measurable_elapsed t)).stronglyMeasurable.integral_prod_left.measurable

lemma Control.measurable_cost_integral {W : BrownianSystem Ω} (γ : OrderParameter)
    (t : ℝ) (ht : t ≤ 1) (α : Control W (Real.toNNReal t)) :
    Measurable (fun ω => ∫ s in t..1, extend γ.val s * (α.val (Real.toNNReal (s - t)) ω)^2) := by
  simp_rw [intervalIntegral.integral_of_le ht]
  exact ((γ.measurable_extend.comp measurable_fst).mul
    ((α.measurable_elapsed t).pow_const 2)).stronglyMeasurable.integral_prod_left.measurable

lemma Control.drift_integral_bound {W : BrownianSystem Ω} (γ : OrderParameter)
    (t : ℝ) (ht : t ≤ 1) (α : Control W (Real.toNNReal t)) (ω : Ω) :
    |∫ s in t..1, extend γ.val s * α.val (Real.toNNReal (s - t)) ω| ≤
      ∫ s in t..1, extend γ.val s := by
  rw [← Real.norm_eq_abs]
  apply intervalIntegral.norm_integral_le_of_norm_le ht _ γ.integrable.intervalIntegrable
  exact Filter.Eventually.of_forall (fun s _ => by
    simp only [Real.norm_eq_abs, abs_mul, γ.abs_extend]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (α.bound _ _) (γ.extend_nonneg s))

lemma Control.cost_integral_bound {W : BrownianSystem Ω} (γ : OrderParameter)
    (t : ℝ) (ht : t ≤ 1) (α : Control W (Real.toNNReal t)) (ω : Ω) :
    |∫ s in t..1, extend γ.val s * (α.val (Real.toNNReal (s - t)) ω)^2| ≤
      ∫ s in t..1, extend γ.val s := by
  rw [← Real.norm_eq_abs]
  apply intervalIntegral.norm_integral_le_of_norm_le ht _ γ.integrable.intervalIntegrable
  exact Filter.Eventually.of_forall (fun s _ => by
    simp only [Real.norm_eq_abs, abs_mul, γ.abs_extend, abs_pow]
    simpa only [one_pow, mul_one] using mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (abs_nonneg _) (α.bound _ _) 2) (γ.extend_nonneg s))

lemma controlPayoff_measurable (W : BrownianSystem Ω) (γ : OrderParameter)
    (t x : ℝ) (ht : t ≤ 1) (α : Control W (Real.toNNReal t)) :
    Measurable (controlPayoff W γ t x α) := by
  exact (((measurable_const.add (W.measurable 1)).sub
    (W.measurable (Real.toNNReal t))).add
    (α.measurable_drift_integral γ t ht)).abs.sub
    ((α.measurable_cost_integral γ t ht).const_mul _)

lemma controlPayoff_abs_bound (W : BrownianSystem Ω) (γ : OrderParameter)
    (t x : ℝ) (ht : t ≤ 1) (α : Control W (Real.toNNReal t)) (ω : Ω) :
    |controlPayoff W γ t x α ω| ≤ |x + W.B 1 ω - W.B (Real.toNNReal t) ω| +
      (3 / 2 : ℝ) * ∫ s in t..1, extend γ.val s := by
  have hd := α.drift_integral_bound γ t ht ω
  have hc := α.cost_integral_bound γ t ht ω
  have htri := abs_add_le (x + W.B 1 ω - W.B (Real.toNNReal t) ω)
    (∫ s in t..1, extend γ.val s * α.val (Real.toNNReal (s - t)) ω)
  have hall := abs_sub
    |x + W.B 1 ω - W.B (Real.toNNReal t) ω +
      ∫ s in t..1, extend γ.val s * α.val (Real.toNNReal (s - t)) ω|
    ((1 / 2 : ℝ) * ∫ s in t..1, extend γ.val s * (α.val (Real.toNNReal (s - t)) ω)^2)
  simp only [abs_abs, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)] at hall
  dsimp [controlPayoff]
  linarith

lemma controlPayoff_integrable (W : BrownianSystem Ω) (γ : OrderParameter)
    (t x : ℝ) (ht : t ≤ 1) (α : Control W (Real.toNNReal t)) :
    Integrable (controlPayoff W γ t x α) W.law := by
  let := W.isProbability
  have h := (((integrable_const x).add (W.brownian.integrable_eval 1)).sub
    (W.brownian.integrable_eval (Real.toNNReal t))).abs.add
    (integrable_const ((3 / 2 : ℝ) * ∫ s in t..1, extend γ.val s))
  exact h.mono' (controlPayoff_measurable W γ t x ht α).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun ω => controlPayoff_abs_bound W γ t x ht α ω))

lemma controlPayoff_le (W : BrownianSystem Ω) (γ : OrderParameter)
    (t x : ℝ) (ht : t ≤ 1) (α : Control W (Real.toNNReal t)) (ω : Ω) :
    controlPayoff W γ t x α ω ≤ |x + W.B 1 ω - W.B (Real.toNNReal t) ω| +
      (1 / 2 : ℝ) * ∫ s in t..1, extend γ.val s := by
  have habs : Integrable (fun s : ℝ => extend γ.val s * |α.val (Real.toNNReal (s - t)) ω|) := by
    exact γ.integrable.mul_bdd
      (((α.measurable_elapsed t).comp measurable_prodMk_right).abs.aestronglyMeasurable)
      (Filter.Eventually.of_forall (fun s => by
        simpa only [Real.norm_eq_abs, Function.comp_apply, abs_abs] using α.bound _ _))
  have hnorm : |∫ s in t..1, extend γ.val s * α.val (Real.toNNReal (s - t)) ω| ≤
      ∫ s in t..1, extend γ.val s * |α.val (Real.toNNReal (s - t)) ω| := by
    simpa only [Real.norm_eq_abs, abs_mul, γ.abs_extend] using
      (intervalIntegral.norm_integral_le_integral_norm (f := fun s =>
        extend γ.val s * α.val (Real.toNNReal (s - t)) ω) ht)
  have hcomp := intervalIntegral.integral_mono_on ht
    (habs.sub ((α.integrable_weighted_sq γ t ω).const_mul (1 / 2 : ℝ))).intervalIntegrable
    (γ.integrable.const_mul (1 / 2 : ℝ)).intervalIntegrable
    (fun s (_ : s ∈ Set.Icc t 1) => show
      extend γ.val s * |α.val (Real.toNNReal (s - t)) ω| -
          (1 / 2 : ℝ) * (extend γ.val s * (α.val (Real.toNNReal (s - t)) ω)^2) ≤
        (1 / 2 : ℝ) * extend γ.val s from by
      have he : |α.val (Real.toNNReal (s - t)) ω| -
          (1 / 2 : ℝ) * (α.val (Real.toNNReal (s - t)) ω)^2 ≤ 1 / 2 := by
        nlinarith [sq_nonneg (|α.val (Real.toNNReal (s - t)) ω| - 1),
          sq_abs (α.val (Real.toNNReal (s - t)) ω)]
      nlinarith [mul_le_mul_of_nonneg_left he (γ.extend_nonneg s)])
  simp only [Pi.sub_apply] at hcomp
  rw [intervalIntegral.integral_sub habs.intervalIntegrable
    ((α.integrable_weighted_sq γ t ω).const_mul (1 / 2 : ℝ)).intervalIntegrable,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hcomp
  have htri := abs_add_le (x + W.B 1 ω - W.B (Real.toNNReal t) ω)
    (∫ s in t..1, extend γ.val s * α.val (Real.toNNReal (s - t)) ω)
  dsimp [controlPayoff]
  linarith

end ZeroTemperatureSK

end
end

end OAI
