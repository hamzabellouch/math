import Mathlib
import OAI.Geometry.WeakHessian.Entropy.FiniteEntropy

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Filter
open Set Filter MeasureTheory InformationTheory
open Set Filter
open scoped Topology
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set Filter Topology

namespace WeakHessian
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BoundedContinuousFunction

lemma mul_log_fenchel {r a : ℝ} (hr : 0 ≤ r) : r*a-Real.exp a+r ≤ r*Real.log r := by
  rcases hr.eq_or_lt with hr|hr
  · simp only [← hr,zero_mul,add_zero,sub_nonpos]
    exact (Real.exp_pos _).le
  · have H := Real.log_le_sub_one_of_pos (div_pos (Real.exp_pos a) hr)
    rw [Real.log_div (Real.exp_pos _).ne' hr.ne',Real.log_exp] at H
    have := (mul_le_mul_of_nonneg_left H hr.le)
    simp only [mul_sub,mul_div_cancel₀ _ hr.ne',mul_one] at this
    nlinarith

lemma mul_log_floor_gap {r δ : ℝ} (hr : 0 ≤ r) (hδ : 0 < δ) :
    r*Real.log r - (r*Real.log (max δ r)-max δ r+r) ≤ δ := by
  by_cases h : δ ≤ r
  · rw [max_eq_right h]
    linarith
  · have hrd : r ≤ δ := (le_of_not_ge h)
    rw [max_eq_left hrd]
    rcases hr.eq_or_lt with hr|hr
    · simp [← hr]
    · have H := mul_le_mul_of_nonneg_left (Real.log_le_log hr hrd) hr.le
      nlinarith

lemma exp_sub_bound {a b M : ℝ} (ha : a ≤ M) (hb : b ≤ M) :
    ‖Real.exp a-Real.exp b‖ ≤ Real.exp M*‖a-b‖ := by
  apply (convex_Iic M).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) ?_ hb ha
  intro x hx
  simpa only [Real.norm_eq_abs,abs_of_pos (Real.exp_pos x)] using Real.exp_le_exp.mpr hx

lemma min_sub_clamp {x a b : ℝ} (ha : a ≤ b) : ‖a-min x b‖ ≤ ‖a-x‖ := by
  simp only [Real.norm_eq_abs]
  by_cases hx : x ≤ b
  · simp [min_eq_left hx]
  · rw [min_eq_right (le_of_not_ge hx),abs_of_nonpos (sub_nonpos.mpr ha),
      abs_of_nonpos (sub_nonpos.mpr (ha.trans (le_of_not_ge hx)))]
    linarith

universe u
variable {X : Type u} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {m μ : Measure X} [IsFiniteMeasure m] [IsFiniteMeasure μ]

lemma entropyReal_fenchel (hμ : FiniteEntropy m μ) (f : X →ᵇ ℝ) :
    (∫ x, f x ∂μ) - (∫ x, Real.exp (f x) ∂m) + μ.real univ ≤ entropyReal m μ := by
  have hfμ : Integrable (fun x => f x) μ := f.integrable μ
  have hm : Integrable (fun x => (μ.rnDeriv m x).toReal*f x) m :=
    (integrable_toReal_rnDeriv_mul_iff hμ.1).mpr hfμ
  have hr : Integrable (fun x => (μ.rnDeriv m x).toReal) m := by
    simpa only [mul_one] using (integrable_toReal_rnDeriv_mul_iff hμ.1).mpr (integrable_const (1:ℝ))
  have he : Integrable (fun x => Real.exp (f x)) m := by
    apply (integrable_const (Real.exp ‖f‖)).mono'
      (Real.continuous_exp.comp f.continuous).aestronglyMeasurable
    exact ae_of_all _ fun x => by
      simp only [Function.comp_apply,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr (le_trans (le_abs_self _) (f.norm_coe_le_norm x))
  have hlog : Integrable (fun x => (μ.rnDeriv m x).toReal * Real.log (μ.rnDeriv m x).toReal) m :=
    (integrable_rnDeriv_mul_log_iff hμ.1).mpr hμ.2
  have H := integral_mono (hm.sub he |>.add hr) hlog (fun x => mul_log_fenchel ENNReal.toReal_nonneg)
  simp only [Pi.add_apply,Pi.sub_apply] at H
  rw [integral_add (f := fun x => (μ.rnDeriv m x).toReal*f x-Real.exp (f x)) (hm.sub he) hr,integral_sub hm he,integral_toReal_rnDeriv_mul hμ.1,
    Measure.integral_toReal_rnDeriv hμ.1,← entropyReal_eq_integral_density hμ.1] at H
  exact H

end WeakHessian

end
end InlinedFile0

end OAI
