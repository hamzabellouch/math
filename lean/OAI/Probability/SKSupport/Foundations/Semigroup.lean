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
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat

def semigroup (h : ℝ≥0) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ y : ℝ, f (x+y) ∂gaussianReal 0 h

def logSemigroup (c : ℝ) (h : ℝ≥0) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  if c = 0 then semigroup h f x else Real.log (semigroup h (fun z => Real.exp (c*f z)) x) / c

lemma integrable_exp_abs (c : ℝ) (μ : ℝ) (h : ℝ≥0) :
    Integrable (fun y : ℝ => Real.exp (c*|y|)) (gaussianReal μ h) := by
  apply Integrable.mono' ((integrable_exp_mul_gaussianReal (μ := μ) (v := h) c).add
    (integrable_exp_mul_gaussianReal (μ := μ) (v := h) (-c)))
    (by fun_prop)
  filter_upwards [] with y
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  by_cases hy : 0 ≤ y
  · rw [abs_of_nonneg hy]
    exact le_add_of_nonneg_right (Real.exp_nonneg _)
  · rw [abs_of_neg (lt_of_not_ge hy)]
    have he : c*(-y) = (-c)*y := by ring
    rw [he]
    exact le_add_of_nonneg_left (Real.exp_nonneg _)

lemma integrable_translate_of_lipschitz {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (h : ℝ≥0) (x : ℝ) :
    Integrable (fun y => f (x+y)) (gaussianReal 0 h) := by
  apply Integrable.mono' ((integrable_const ‖f x‖).add
    (((memLp_id_gaussianReal (μ := 0) (v := h) 1).integrable (by simp)).norm.const_mul (K:ℝ)))
    (hf.continuous.measurable.comp (measurable_const.add measurable_id) |>.aestronglyMeasurable)
  filter_upwards [] with y
  have hb := hf.norm_sub_le (x+y) x
  have hh := norm_sub_le (f (x+y)) (f x)
  have hh' := norm_add_le (f (x+y)-f x) (f x)
  simp only [add_sub_cancel_left, sub_add_cancel] at hb hh'
  change ‖f (x+y)‖ ≤ ‖f x‖+(K:ℝ)*‖y‖
  linarith

lemma integrable_exp_translate_of_lipschitz {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (c : ℝ) (h : ℝ≥0) (x : ℝ) :
    Integrable (fun y => Real.exp (c*f (x+y))) (gaussianReal 0 h) := by
  apply Integrable.mono' ((integrable_exp_abs (|c| * (K:ℝ)) 0 h).const_mul (Real.exp (c*f x)))
    ((measurable_const.mul (hf.continuous.measurable.comp (measurable_const.add measurable_id))).exp.aestronglyMeasurable)
  filter_upwards [] with y
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h₁ := hf.norm_sub_le (x+y) x
  simp only [Real.norm_eq_abs, add_sub_cancel_left] at h₁
  have h₂ : c*(f (x+y)-f x) ≤ |c| * |f (x+y)-f x| := by
    calc
      _ ≤ |c*(f (x+y)-f x)| := le_abs_self _
      _ = _ := abs_mul _ _
  have h₃ := mul_le_mul_of_nonneg_left h₁ (abs_nonneg c)
  change c*f (x+y) ≤ c*f x+(|c| * (K:ℝ))*|y|
  nlinarith

lemma semigroup_exp_pos {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (c : ℝ) (h : ℝ≥0) (x : ℝ) :
    0 < semigroup h (fun z => Real.exp (c*f z)) x := by
  unfold semigroup
  exact integral_pos_iff_support_of_nonneg (fun y => (Real.exp_pos _).le)
    (integrable_exp_translate_of_lipschitz hf c h x) |>.mpr (by simp [Function.support])

end ZeroTemperatureSK.Heat

namespace ZeroTemperatureSK.Heat

lemma semigroup_lipschitz {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (h : ℝ≥0) : LipschitzWith K (semigroup h f) := by
  apply LipschitzWith.of_dist_le_mul
  intro x z
  rw [Real.dist_eq, Real.dist_eq]
  unfold semigroup
  rw [← integral_sub (integrable_translate_of_lipschitz hf h x)
    (integrable_translate_of_lipschitz hf h z)]
  calc
    _ ≤ ∫ y, |f (x+y)-f (z+y)| ∂gaussianReal 0 h := abs_integral_le_integral_abs
    _ ≤ ∫ _y, (K:ℝ)*|x-z| ∂gaussianReal 0 h := by
      apply integral_mono ((integrable_translate_of_lipschitz hf h x).sub
        (integrable_translate_of_lipschitz hf h z)).abs (integrable_const _)
      intro y
      change |f (x+y)-f (z+y)| ≤ (K:ℝ)*|x-z|
      simpa only [Real.norm_eq_abs, add_sub_add_right_eq_sub] using hf.norm_sub_le (x+y) (z+y)
    _ = _ := by simp

lemma logSemigroup_sub_le {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) {c : ℝ} (hc : 0 < c) (h : ℝ≥0) (x z : ℝ) :
    logSemigroup c h f x-logSemigroup c h f z ≤ (K:ℝ)*|x-z| := by
  have hx := semigroup_exp_pos hf c h x
  have hz := semigroup_exp_pos hf c h z
  have hE : semigroup h (fun w => Real.exp (c*f w)) x ≤
      Real.exp (c*((K:ℝ)*|x-z|))*semigroup h (fun w => Real.exp (c*f w)) z := by
    unfold semigroup
    rw [← integral_const_mul]
    apply integral_mono (integrable_exp_translate_of_lipschitz hf c h x)
      ((integrable_exp_translate_of_lipschitz hf c h z).const_mul _)
    intro y
    change Real.exp (c*f (x+y)) ≤ Real.exp (c*((K:ℝ)*|x-z|))*Real.exp (c*f (z+y))
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hh := hf.norm_sub_le (x+y) (z+y)
    simp only [Real.norm_eq_abs, add_sub_add_right_eq_sub] at hh
    have hh' := (le_abs_self (f (x+y)-f (z+y))).trans hh
    nlinarith
  have hlog := Real.log_le_log hx hE
  rw [Real.log_mul (Real.exp_ne_zero _) (ne_of_gt hz), Real.log_exp] at hlog
  simp only [logSemigroup, ne_of_gt hc, ↓reduceIte]
  rw [← sub_div, div_le_iff₀ hc]
  nlinarith

lemma logSemigroup_lipschitz {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) {c : ℝ} (hc : 0 ≤ c) (h : ℝ≥0) :
    LipschitzWith K (logSemigroup c h f) := by
  by_cases hc0 : c = 0
  · subst c
    have he : logSemigroup 0 h f = semigroup h f := by
      funext x
      simp only [logSemigroup, ↓reduceIte]
    rw [he]
    exact semigroup_lipschitz hf h
  · have hcp : 0 < c := lt_of_le_of_ne hc (Ne.symm hc0)
    apply LipschitzWith.of_dist_le_mul
    intro x z
    rw [Real.dist_eq, Real.dist_eq, abs_le]
    constructor
    · have he := logSemigroup_sub_le hf hcp h z x
      rw [abs_sub_comm z x] at he
      linarith
    · exact logSemigroup_sub_le hf hcp h x z

lemma semigroup_even {f : ℝ → ℝ} (hf : Measurable f) (he : Function.Even f)
    (h : ℝ≥0) : Function.Even (semigroup h f) := by
  intro x
  have hn : HasLaw (fun y : ℝ => -y) (gaussianReal 0 h) (gaussianReal 0 h) := by
    constructor
    · exact measurable_neg.aemeasurable
    · simpa using gaussianReal_map_neg (μ := 0) (v := h)
  have hh := hn.integral_comp (f := fun y => f (-x+y))
    (hf.comp (measurable_const.add measurable_id) |>.aestronglyMeasurable)
  change (∫ y : ℝ, f (-x + -y) ∂gaussianReal 0 h) = semigroup h f (-x) at hh
  rw [← hh]
  unfold semigroup
  apply integral_congr_ae
  filter_upwards [] with y
  rw [← neg_add, he]

lemma logSemigroup_even {f : ℝ → ℝ} (hf : Measurable f) (he : Function.Even f)
    (c : ℝ) (h : ℝ≥0) : Function.Even (logSemigroup c h f) := by
  intro x
  by_cases hc : c = 0
  · simp only [logSemigroup, hc, ↓reduceIte, semigroup_even hf he h x]
  · have hhe : Function.Even (fun z => Real.exp (c*f z)) := by
      intro z
      change Real.exp (c*f (-z)) = Real.exp (c*f z)
      rw [he]
    simp only [logSemigroup, hc, ↓reduceIte]
    exact congrArg (fun v : ℝ => Real.log v/c)
      (semigroup_even (measurable_const.mul hf |>.exp) hhe h x)

end ZeroTemperatureSK.Heat

end
end
end
end

end OAI
