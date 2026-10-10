import Mathlib
import OAI.Probability.SKSupport.Model

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK.WeakIto
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
variable {B : ℝ≥0 → Ω → ℝ}

lemma adapted_indep_increment (hB : IsPreBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (s h : ℝ≥0) {Y : Ω → ℝ}
    (hY : Measurable[Filtration.natural B (fun t => (hm t).stronglyMeasurable) s] Y) :
    IndepFun Y (fun ω => B (s+h) ω - B s ω) P := by
  have hi := (hB.indepFun_shift s).comp (measurable_pi_apply h) measurable_id
  change IndepFun (fun ω => B (s+h) ω - B s ω)
    (fun ω (t : Set.Iic s) => B t ω) P at hi
  apply Indep.symm
  apply indep_of_indep_of_le hi le_rfl
  rw [← Filtration.natural_eq_comap B (fun t => (hm t).stronglyMeasurable) s]
  exact measurable_iff_comap_le.mp hY

lemma integral_adapted_mul_increment (hB : IsPreBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (s h : ℝ≥0) {Y : Ω → ℝ}
    (hY : Measurable[Filtration.natural B (fun t => (hm t).stronglyMeasurable) s] Y) :
    (∫ ω, Y ω * (B (s+h) ω - B s ω) ∂P) = 0 := by
  have hYm : Measurable Y := hY.mono
    ((Filtration.natural B (fun t => (hm t).stronglyMeasurable)).le s) le_rfl
  rw [(adapted_indep_increment hB hm s h hY).integral_fun_mul_eq_mul_integral
    hYm.aestronglyMeasurable ((hm (s+h)).sub (hm s)).aestronglyMeasurable]
  rw [integral_sub (hB.integrable_eval _) (hB.integrable_eval _), hB.integral_eval,
    hB.integral_eval]
  simp

lemma gaussian_second_moment (v : ℝ≥0) :
    (∫ x : ℝ, x^2 ∂gaussianReal 0 v) = (v : ℝ) := by
  have h := variance_fun_id_gaussianReal (μ := 0) (v := v)
  rw [variance_eq_integral (X := fun x : ℝ => x) measurable_id'.aemeasurable] at h
  simpa using h

lemma integral_adapted_mul_increment_sq (hB : IsPreBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (s h : ℝ≥0) {Y : Ω → ℝ}
    (hY : Measurable[Filtration.natural B (fun t => (hm t).stronglyMeasurable) s] Y) :
    (∫ ω, Y ω * (B (s+h) ω - B s ω)^2 ∂P) = (h : ℝ) * ∫ ω, Y ω ∂P := by
  have hYm : Measurable Y := hY.mono
    ((Filtration.natural B (fun t => (hm t).stronglyMeasurable)).le s) le_rfl
  have hi := (adapted_indep_increment hB hm s h hY).comp measurable_id
    (measurable_id.pow_const 2)
  change IndepFun Y (fun ω => (B (s+h) ω - B s ω)^2) P at hi
  rw [hi.integral_fun_mul_eq_mul_integral hYm.aestronglyMeasurable
    (((hm (s+h)).sub (hm s)).pow_const 2).aestronglyMeasurable]
  have he := (hB.hasLaw_sub (s+h) s).integral_comp
    (f := fun x : ℝ => x^2) ((measurable_id.pow_const 2).aestronglyMeasurable)
  change (∫ ω, (B (s+h) ω - B s ω)^2 ∂P) = _ at he
  rw [he, gaussian_second_moment]
  rw [coe_nndist, Real.dist_eq]
  change (∫ ω, Y ω ∂P) * |((s+h : ℝ≥0) : ℝ) - (s : ℝ)| = _
  rw [NNReal.coe_add, add_sub_cancel_left, abs_of_nonneg h.coe_nonneg]
  ring

end ZeroTemperatureSK.WeakIto

namespace ZeroTemperatureSK.WeakIto

lemma taylor2_bound {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f) {C : ℝ}
    (hC : ∀ x, |iteratedDeriv 3 f x| ≤ C) (x d : ℝ) :
    |f (x+d) - f x - deriv f x*d - (1/2:ℝ)*deriv (deriv f) x*d^2| ≤
      C / 6 * |d|^3 := by
  by_cases hd : d = 0
  · simp [hd]
  have hxd : x ≠ x+d := by intro h; apply hd; linarith
  obtain ⟨y, hy, he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (n := 2) hxd hf.contDiffOn
  have hu := uniqueDiffOn_uIcc hxd
  have hx : x ∈ Set.uIcc x (x+d) := left_mem_uIcc
  have h1 : iteratedDerivWithin 1 f (Set.uIcc x (x+d)) x = deriv f x := by
    rw [iteratedDerivWithin_eq_iteratedDeriv hu (hf.of_le (by norm_num)).contDiffAt hx,
      iteratedDeriv_one]
  have h2 : iteratedDerivWithin 2 f (Set.uIcc x (x+d)) x = deriv (deriv f) x := by
    rw [iteratedDerivWithin_eq_iteratedDeriv hu (hf.of_le (by norm_num)).contDiffAt hx,
      iteratedDeriv_succ, iteratedDeriv_one]
  simp only [taylorWithinEval_succ, taylor_within_zero_eval, h1, h2] at he
  norm_num at he
  have he' : f (x+d) - f x - deriv f x*d - (1/2:ℝ)*deriv (deriv f) x*d^2 =
      iteratedDeriv 3 f y * d^3 / 6 := by
    calc
      _ = f (x+d) - (f x + d * deriv f x + (1/2:ℝ)*d^2*deriv (deriv f) x) := by ring
      _ = _ := by convert he using 1
  rw [he', abs_div, abs_mul, abs_pow]
  norm_num
  have := mul_le_mul_of_nonneg_right (hC y) (pow_nonneg (abs_nonneg d) 3)
  nlinarith

end ZeroTemperatureSK.WeakIto

end
end
end

end OAI
