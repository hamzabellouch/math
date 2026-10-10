import Mathlib
import OAI.Probability.SKSupport.Foundations.Semigroup

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat

lemma exp_translate_local_bound {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) {c : ℝ} (hc : 0 ≤ c) (x z y : ℝ)
    (hz : |z-x| ≤ 1) :
    Real.exp (c*f (z+y)) ≤
      Real.exp (c*f x+c*(K:ℝ))*Real.exp ((c*(K:ℝ))*|y|) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hfz := hf.norm_sub_le (z+y) x
  simp only [Real.norm_eq_abs] at hfz
  have hz' : |z+y-x| ≤ 1+|y| := by
    have he : z+y-x = (z-x)+y := by ring
    rw [he]
    exact (abs_add_le _ _).trans (by linarith)
  have h₁ := mul_le_mul_of_nonneg_left hz' K.coe_nonneg
  have h₂ := (le_abs_self (f (z+y)-f x)).trans (hfz.trans h₁)
  nlinarith [mul_le_mul_of_nonneg_left h₂ hc]

lemma hasDerivAt_semigroup_exp {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : ContDiff ℝ 1 f) (hLip : LipschitzWith K f) {c : ℝ} (hc : 0 ≤ c)
    (h : ℝ≥0) (x : ℝ) :
    HasDerivAt (semigroup h (fun z => Real.exp (c*f z)))
      (∫ y, c*deriv f (x+y)*Real.exp (c*f (x+y)) ∂gaussianReal 0 h) x := by
  have hdf : Continuous (deriv f) := hf.continuous_deriv (by norm_num)
  let bound (y : ℝ) := c*(K:ℝ)*Real.exp (c*f x+c*(K:ℝ))*Real.exp ((c*(K:ℝ))*|y|)
  have hb : Integrable bound (gaussianReal 0 h) :=
    (integrable_exp_abs (c*(K:ℝ)) 0 h).const_mul _
  have hi := integrable_exp_translate_of_lipschitz hLip c h x
  have hm : ∀ᶠ z in 𝓝 x,
      AEStronglyMeasurable (fun y => Real.exp (c*f (z+y))) (gaussianReal 0 h) :=
    Filter.Eventually.of_forall (fun z => by
      exact (measurable_const.mul (hf.continuous.measurable.comp
        (measurable_const.add measurable_id))).exp.aestronglyMeasurable)
  have hdm : AEStronglyMeasurable
      (fun y => c*deriv f (x+y)*Real.exp (c*f (x+y))) (gaussianReal 0 h) := by
    exact ((measurable_const.mul (hdf.measurable.comp (measurable_const.add measurable_id))).mul
      (measurable_const.mul (hf.continuous.measurable.comp
        (measurable_const.add measurable_id))).exp).aestronglyMeasurable
  have hbound : ∀ᵐ y ∂gaussianReal 0 h, ∀ z ∈ Metric.ball x 1,
      ‖c*deriv f (z+y)*Real.exp (c*f (z+y))‖ ≤ bound y := by
    filter_upwards [] with y z hz
    have hz' : |z-x| ≤ 1 := by simpa only [Metric.mem_ball, Real.dist_eq] using le_of_lt hz
    have hD : |deriv f (z+y)| ≤ K := by
      simpa only [Real.norm_eq_abs] using norm_deriv_le_of_lipschitz (x₀ := z+y) hLip
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hc,
      abs_of_pos (Real.exp_pos _)]
    change c*|deriv f (z+y)| * Real.exp (c*f (z+y)) ≤
      c*(K:ℝ)*Real.exp (c*f x+c*(K:ℝ))*Real.exp ((c*(K:ℝ))*|y|)
    calc
      _ ≤ c*(K:ℝ)*Real.exp (c*f (z+y)) := by gcongr
      _ ≤ _ := by
        have he := mul_le_mul_of_nonneg_left (exp_translate_local_bound hLip hc x z y hz')
          (mul_nonneg hc K.coe_nonneg)
        simpa only [mul_assoc] using he
  have hdiff : ∀ᵐ y ∂gaussianReal 0 h, ∀ z ∈ Metric.ball x 1,
      HasDerivAt (fun w => Real.exp (c*f (w+y)))
        (c*deriv f (z+y)*Real.exp (c*f (z+y))) z := by
    filter_upwards [] with y z hz
    have h1 : HasDerivAt (fun w => f (w+y)) (deriv f (z+y)) z := by
      convert (hf.differentiable (by norm_num) (z+y)).hasDerivAt.comp z
        ((hasDerivAt_id z).add_const y) using 1 <;> first | rfl | simp
    have h2 := (h1.const_mul c).exp
    convert h2 using 1
    ring
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds x (by norm_num : (0:ℝ)<1)) hm hi hdm hbound hb hdiff).2

lemma hasDerivAt_logSemigroup {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : ContDiff ℝ 1 f) (hLip : LipschitzWith K f) {c : ℝ} (hc : 0 < c)
    (h : ℝ≥0) (x : ℝ) :
    HasDerivAt (logSemigroup c h f)
      ((∫ y, deriv f (x+y)*Real.exp (c*f (x+y)) ∂gaussianReal 0 h) /
        semigroup h (fun z => Real.exp (c*f z)) x) x := by
  have hd := hasDerivAt_semigroup_exp hf hLip hc.le h x
  have he : (∫ y, c*deriv f (x+y)*Real.exp (c*f (x+y)) ∂gaussianReal 0 h) =
      c*(∫ y, deriv f (x+y)*Real.exp (c*f (x+y)) ∂gaussianReal 0 h) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with y
    ring
  rw [he] at hd
  have hh := ((hd.log (ne_of_gt (semigroup_exp_pos hLip c h x))).div_const c)
  have hfun : logSemigroup c h f = fun z =>
      Real.log (semigroup h (fun w => Real.exp (c*f w)) z)/c := by
    funext z
    simp only [logSemigroup, ne_of_gt hc, ↓reduceIte]
  rw [hfun]
  convert hh using 1
  first | rfl | field_simp [ne_of_gt hc]

end ZeroTemperatureSK.Heat

namespace ZeroTemperatureSK.Heat

lemma integrable_weight_exp_translate {f g : ℝ → ℝ} {K G : ℝ≥0}
    (hf : LipschitzWith K f) (hg : Measurable g) (hG : ∀ z, |g z| ≤ G)
    (c : ℝ) (h : ℝ≥0) (x : ℝ) :
    Integrable (fun y => g (x+y)*Real.exp (c*f (x+y))) (gaussianReal 0 h) := by
  apply (integrable_exp_translate_of_lipschitz hf c h x).bdd_mul
    (hg.comp (measurable_const.add measurable_id)).aestronglyMeasurable
  filter_upwards [] with y
  change ‖g (x+y)‖ ≤ (G:ℝ)
  simpa only [Real.norm_eq_abs] using hG (x+y)

lemma hasDerivAt_semigroup_weight_exp {f g : ℝ → ℝ} {K G G₁ : ℝ≥0}
    (hf : ContDiff ℝ 1 f) (hLip : LipschitzWith K f)
    (hg : ContDiff ℝ 1 g) (hG : ∀ z, |g z| ≤ G) (hG₁ : ∀ z, |deriv g z| ≤ G₁)
    {c : ℝ} (hc : 0 ≤ c) (h : ℝ≥0) (x : ℝ) :
    HasDerivAt (semigroup h (fun z => g z*Real.exp (c*f z)))
      (∫ y, (deriv g (x+y)+c*g (x+y)*deriv f (x+y))*Real.exp (c*f (x+y))
        ∂gaussianReal 0 h) x := by
  have hdf : Continuous (deriv f) := hf.continuous_deriv_one
  have hdg : Continuous (deriv g) := hg.continuous_deriv_one
  let C : ℝ := (G₁:ℝ)+c*(G:ℝ)*(K:ℝ)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  let bound (y : ℝ) := C*Real.exp (c*f x+c*(K:ℝ))*Real.exp ((c*(K:ℝ))*|y|)
  have hb : Integrable bound (gaussianReal 0 h) :=
    (integrable_exp_abs (c*(K:ℝ)) 0 h).const_mul _
  have hi := integrable_weight_exp_translate hLip hg.continuous.measurable hG c h x
  have hm : ∀ᶠ z in 𝓝 x, AEStronglyMeasurable
      (fun y => g (z+y)*Real.exp (c*f (z+y))) (gaussianReal 0 h) := by
    filter_upwards [] with z
    exact ((hg.continuous.measurable.comp (measurable_const.add measurable_id)).mul
      ((measurable_const.mul (hf.continuous.measurable.comp
        (measurable_const.add measurable_id))).exp)).aestronglyMeasurable
  have hdm : AEStronglyMeasurable (fun y =>
      (deriv g (x+y)+c*g (x+y)*deriv f (x+y))*Real.exp (c*f (x+y))) (gaussianReal 0 h) := by
    exact ((hdg.measurable.comp (measurable_const.add measurable_id)).add
      ((measurable_const.mul (hg.continuous.measurable.comp (measurable_const.add measurable_id))).mul
        (hdf.measurable.comp (measurable_const.add measurable_id))) |>.mul
      ((measurable_const.mul (hf.continuous.measurable.comp
        (measurable_const.add measurable_id))).exp)).aestronglyMeasurable
  have hbound : ∀ᵐ y ∂gaussianReal 0 h, ∀ z ∈ Metric.ball x 1,
      ‖(deriv g (z+y)+c*g (z+y)*deriv f (z+y))*Real.exp (c*f (z+y))‖ ≤ bound y := by
    filter_upwards [] with y z hz
    have hz' : |z-x| ≤ 1 := by simpa only [Metric.mem_ball, Real.dist_eq] using le_of_lt hz
    have hD : |deriv f (z+y)| ≤ K := by
      simpa only [Real.norm_eq_abs] using norm_deriv_le_of_lipschitz (x₀ := z+y) hLip
    have hw : |deriv g (z+y)+c*g (z+y)*deriv f (z+y)| ≤ C := by
      calc
        _ ≤ |deriv g (z+y)|+|c*g (z+y)*deriv f (z+y)| := abs_add_le _ _
        _ = |deriv g (z+y)|+c*|g (z+y)| * |deriv f (z+y)| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hc]
        _ ≤ C := by dsimp only [C]; gcongr; exact hG₁ _; exact hG _
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ C*Real.exp (c*f (z+y)) := mul_le_mul_of_nonneg_right hw (Real.exp_nonneg _)
      _ ≤ bound y := by
        have he := mul_le_mul_of_nonneg_left (exp_translate_local_bound hLip hc x z y hz') hC
        simpa only [bound, mul_assoc] using he
  have hdiff : ∀ᵐ y ∂gaussianReal 0 h, ∀ z ∈ Metric.ball x 1,
      HasDerivAt (fun w => g (w+y)*Real.exp (c*f (w+y)))
        ((deriv g (z+y)+c*g (z+y)*deriv f (z+y))*Real.exp (c*f (z+y))) z := by
    filter_upwards [] with y z hz
    have h1 : HasDerivAt (fun w => f (w+y)) (deriv f (z+y)) z := by
      convert (hf.differentiable (by norm_num) (z+y)).hasDerivAt.comp z
        ((hasDerivAt_id z).add_const y) using 1 <;> first | rfl | simp
    have h2 : HasDerivAt (fun w => g (w+y)) (deriv g (z+y)) z := by
      convert (hg.differentiable (by norm_num) (z+y)).hasDerivAt.comp z
        ((hasDerivAt_id z).add_const y) using 1 <;> first | rfl | simp
    convert h2.mul (h1.const_mul c).exp using 1
    first | rfl | ring
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds x (by norm_num : (0:ℝ)<1)) hm hi hdm hbound hb hdiff).2

lemma hasDerivAt_semigroup {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : ContDiff ℝ 1 f) (hLip : LipschitzWith K f) (h : ℝ≥0) (x : ℝ) :
    HasDerivAt (semigroup h f) (semigroup h (deriv f) x) x := by
  have hdf : Continuous (deriv f) := hf.continuous_deriv_one
  have hm : ∀ᶠ z in 𝓝 x, AEStronglyMeasurable (fun y => f (z+y)) (gaussianReal 0 h) :=
    Filter.Eventually.of_forall (fun z => (hf.continuous.measurable.comp
      (measurable_const.add measurable_id)).aestronglyMeasurable)
  have hdm : AEStronglyMeasurable (fun y => deriv f (x+y)) (gaussianReal 0 h) :=
    (hdf.measurable.comp (measurable_const.add measurable_id)).aestronglyMeasurable
  have hbound : ∀ᵐ y ∂gaussianReal 0 h, ∀ z ∈ Metric.ball x 1,
      ‖deriv f (z+y)‖ ≤ (K:ℝ) := by
    filter_upwards [] with y z hz
    exact norm_deriv_le_of_lipschitz hLip
  have hdiff : ∀ᵐ y ∂gaussianReal 0 h, ∀ z ∈ Metric.ball x 1,
      HasDerivAt (fun w => f (w+y)) (deriv f (z+y)) z := by
    filter_upwards [] with y z hz
    convert (hf.differentiable (by norm_num) (z+y)).hasDerivAt.comp z
      ((hasDerivAt_id z).add_const y) using 1 <;> first | rfl | simp
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds x (by norm_num : (0:ℝ)<1)) hm
    (integrable_translate_of_lipschitz hLip h x) hdm hbound (integrable_const _) hdiff).2

end ZeroTemperatureSK.Heat

end
end
end
end

end OAI
