import Mathlib
import OAI.Probability.SKSupport.Foundations.VarianceHeat

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

lemma exponentialBound_of_lipschitz {f : ℝ → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) :
    ExponentialBound f := by
  refine ⟨Real.nnabs (f 0)+K, 1, fun z => ?_⟩
  have hl := hf.norm_sub_le z 0
  have ht := norm_add_le (f z-f 0) (f 0)
  simp only [sub_zero, sub_add_cancel, Real.norm_eq_abs] at hl ht
  have he : |z| ≤ Real.exp |z| := by linarith [Real.add_one_le_exp |z|]
  have he1 : 1 ≤ Real.exp |z| := Real.one_le_exp (abs_nonneg z)
  simp only [NNReal.coe_add, Real.coe_nnabs, NNReal.coe_one, one_mul]
  nlinarith [mul_le_mul_of_nonneg_left he K.coe_nonneg,
    mul_le_mul_of_nonneg_left he1 (abs_nonneg (f 0))]

lemma exponentialBound_exp {f : ℝ → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) (c : ℝ) :
    ExponentialBound (fun z => Real.exp (c*f z)) := by
  refine ⟨⟨Real.exp (c*f 0), (Real.exp_pos _).le⟩, Real.nnabs c*K, fun z => ?_⟩
  rw [abs_of_pos (Real.exp_pos _)]
  change Real.exp (c*f z) ≤ Real.exp (c*f 0)*Real.exp ((|c| *(K:ℝ))*|z|)
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hl := hf.norm_sub_le z 0
  simp only [sub_zero, Real.norm_eq_abs] at hl
  have h₁ : c*(f z-f 0) ≤ |c| *|f z-f 0| := by
    exact (le_abs_self _).trans_eq (abs_mul _ _)
  nlinarith [mul_le_mul_of_nonneg_left hl (abs_nonneg c)]

lemma ExponentialBound.bdd_mul {f g : ℝ → ℝ} (hf : ExponentialBound f)
    {G : ℝ≥0} (hg : ∀ z, |g z| ≤ G) : ExponentialBound (fun z => g z*f z) := by
  obtain ⟨A,K,hf⟩ := hf
  refine ⟨G*A, K, fun z => ?_⟩
  rw [abs_mul]
  have hh := mul_le_mul (hg z) (hf z) (abs_nonneg (f z)) G.coe_nonneg
  simpa only [NNReal.coe_mul, mul_assoc] using hh

lemma hasDerivAt_weightExp {f g : ℝ → ℝ} (hf : RegularDatum f) (hg : BoundedSmooth g)
    (c x : ℝ) : HasDerivAt (fun z => g z*Real.exp (c*f z))
      ((deriv g x+c*g x*deriv f x)*Real.exp (c*f x)) x := by
  have hfd := (hf.smooth.differentiable (by simp) x).hasDerivAt
  have hgd := (hg.smooth.differentiable (by simp) x).hasDerivAt
  convert hgd.mul (hfd.const_mul c).exp using 1
  first | rfl | ring

lemma deriv_weightExp {f g : ℝ → ℝ} (hf : RegularDatum f) (hg : BoundedSmooth g) (c : ℝ) :
    deriv (fun z => g z*Real.exp (c*f z)) = fun x =>
      (deriv g x+c*g x*deriv f x)*Real.exp (c*f x) :=
  funext (fun x => (hasDerivAt_weightExp hf hg c x).deriv)

lemma exp_iteratedDeriv_weight {f : ℝ → ℝ} (hf : RegularDatum f) (c : ℝ) (n : ℕ) :
    ∃ g : ℝ → ℝ, BoundedSmooth g ∧
      iteratedDeriv n (fun z => Real.exp (c*f z)) = fun z => g z*Real.exp (c*f z) := by
  induction n with
  | zero => exact ⟨fun _ => 1, BoundedSmooth.const 1, by funext z; simp⟩
  | succ n IH =>
    obtain ⟨g,hg,he⟩ := IH
    exact ⟨fun z => deriv g z+c*g z*deriv f z, weighted_derivative_boundedSmooth hf hg c,
      by rw [iteratedDeriv_succ, he, deriv_weightExp hf hg c]⟩

lemma exponentialBound_exp_iteratedDeriv {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) (c : ℝ) (n : ℕ) :
    ExponentialBound (iteratedDeriv n (fun z => Real.exp (c*f z))) := by
  obtain ⟨g,hg,he⟩ := exp_iteratedDeriv_weight hf c n
  obtain ⟨G,hG⟩ := hg.bound
  rw [he]
  exact (exponentialBound_exp hLip c).bdd_mul hG

lemma hasDerivWithinAt_varianceHeat_exp {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) (c : ℝ)
    {t : ℝ} (ht : 0 ≤ t) (x : ℝ) :
    HasDerivWithinAt (fun s => varianceHeat s (fun z => Real.exp (c*f z)) x)
      ((1/2:ℝ)*varianceHeat t (deriv (deriv (fun z => Real.exp (c*f z)))) x)
      (Set.Ici 0) t := by
  apply hasDerivWithinAt_varianceHeat
    ((contDiff_const.mul hf.smooth).exp.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) (exponentialBound_exp hLip c)
    (by simpa only [iteratedDeriv_one] using exponentialBound_exp_iteratedDeriv hf hLip c 1)
    (by simpa only [iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_zero] using exponentialBound_exp_iteratedDeriv hf hLip c 2)
    ht x

end ZeroTemperatureSK.Heat

namespace ZeroTemperatureSK.Heat

lemma hasDerivAt_scaled_space {g : ℝ → ℝ} (hgc : ContDiff ℝ 1 g)
    (hg : ExponentialBound g) (hg' : ExponentialBound (deriv g)) (a x : ℝ) :
    HasDerivAt (scaled a g) (scaled a (deriv g) x) x := by
  obtain ⟨A,K,hg'⟩ := hg'
  have hdm := hgc.continuous_deriv_one.measurable
  have hm : ∀ᶠ z in 𝓝 x, AEStronglyMeasurable (fun y => g (z+a*y)) (gaussianReal 0 1) :=
    Filter.Eventually.of_forall (fun z => by fun_prop)
  have hdmeas : AEStronglyMeasurable (fun y => deriv g (x+a*y)) (gaussianReal 0 1) := by fun_prop
  have hb : ∀ᵐ y ∂gaussianReal 0 1, ∀ z ∈ Metric.ball x 1,
      ‖deriv g (z+a*y)‖ ≤
        ((A:ℝ)*Real.exp ((K:ℝ)*(|x|+1)))*Real.exp (((K:ℝ)*|a|)*|y|) := by
    filter_upwards [] with y z hz
    have hz' : |z| ≤ |x|+1 := by
      have ht := abs_add_le (z-x) x
      rw [sub_add_cancel] at ht
      have hd : |z-x| < 1 := by simpa only [Metric.mem_ball, Real.dist_eq] using hz
      linarith
    rw [Real.norm_eq_abs]
    exact (exponentialBound_scaled hg' z a y |a| le_rfl).trans (by gcongr)
  have hD : ∀ᵐ y ∂gaussianReal 0 1, ∀ z ∈ Metric.ball x 1,
      HasDerivAt (fun w => g (w+a*y)) (deriv g (z+a*y)) z := by
    filter_upwards [] with y z hz
    convert (hgc.differentiable (by norm_num) (z+a*y)).hasDerivAt.comp z
      ((hasDerivAt_id z).add_const (a*y)) using 1 <;> first | rfl | simp
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds x (show (0:ℝ)<1 by norm_num)) hm
    (integrable_scaled_of_expBound hgc.continuous.measurable hg a x) hdmeas hb
    ((integrable_exp_abs ((K:ℝ)*|a|) 0 1).const_mul _) hD).2

lemma deriv_varianceHeat {g : ℝ → ℝ} (hgc : ContDiff ℝ 1 g)
    (hg : ExponentialBound g) (hg' : ExponentialBound (deriv g)) (t : ℝ) :
    deriv (varianceHeat t g) = varianceHeat t (deriv g) :=
  funext (fun x => (hasDerivAt_scaled_space hgc hg hg' (Real.sqrt t) x).deriv)

lemma deriv_deriv_varianceHeat {g : ℝ → ℝ} (hgc : ContDiff ℝ 2 g)
    (hg : ExponentialBound g) (hg' : ExponentialBound (deriv g))
    (hg'' : ExponentialBound (deriv (deriv g))) (t : ℝ) :
    deriv (deriv (varianceHeat t g)) = varianceHeat t (deriv (deriv g)) := by
  rw [deriv_varianceHeat (hgc.of_le (by norm_num)) hg hg',
    deriv_varianceHeat (show ContDiff ℝ 1 (deriv g) from hgc.deriv') hg' hg'']

lemma varianceHeat_equation {g : ℝ → ℝ} (hgc : ContDiff ℝ 2 g)
    (hg : ExponentialBound g) (hg' : ExponentialBound (deriv g))
    (hg'' : ExponentialBound (deriv (deriv g))) {t : ℝ} (ht : 0 ≤ t) (x : ℝ) :
    HasDerivWithinAt (fun s => varianceHeat s g x)
      ((1/2:ℝ)*deriv (deriv (varianceHeat t g)) x) (Set.Ici 0) t := by
  rw [deriv_deriv_varianceHeat hgc hg hg' hg'']
  exact hasDerivWithinAt_varianceHeat hgc hg hg' hg'' ht x

end ZeroTemperatureSK.Heat

namespace ZeroTemperatureSK.Heat

lemma logarithmic_heat_equation {g : ℝ → ℝ} (hgc : ContDiff ℝ 2 g)
    (hg : ExponentialBound g) (hg' : ExponentialBound (deriv g))
    (hg'' : ExponentialBound (deriv (deriv g))) {c : ℝ} (hc : c ≠ 0)
    {t : ℝ} (ht : 0 ≤ t) (hpos : ∀ z, 0 < varianceHeat t g z) (x : ℝ) :
    HasDerivWithinAt (fun s => Real.log (varianceHeat s g x)/c)
      ((1/2:ℝ)*deriv (deriv (fun z => Real.log (varianceHeat t g z)/c)) x +
        c/2*(deriv (fun z => Real.log (varianceHeat t g z)/c) x)^2)
      (Set.Ici 0) t := by
  have hdx (z : ℝ) : HasDerivAt (varianceHeat t g) (varianceHeat t (deriv g) z) z :=
    hasDerivAt_scaled_space (hgc.of_le (by norm_num)) hg hg' (Real.sqrt t) z
  have hddx (z : ℝ) : HasDerivAt (varianceHeat t (deriv g))
      (varianceHeat t (deriv (deriv g)) z) z :=
    hasDerivAt_scaled_space (show ContDiff ℝ 1 (deriv g) from hgc.deriv') hg' hg'' (Real.sqrt t) z
  have hdf : deriv (fun z => Real.log (varianceHeat t g z)/c) =
      fun z => (varianceHeat t (deriv g) z/varianceHeat t g z)/c := by
    funext z
    exact ((hdx z).log (ne_of_gt (hpos z)) |>.div_const c).deriv
  have hdd := ((hddx x).div (hdx x) (ne_of_gt (hpos x))).div_const c
  simp only [Pi.div_apply] at hdd
  have htime := ((hasDerivWithinAt_varianceHeat hgc hg hg' hg'' ht x).log
    (ne_of_gt (hpos x))).div_const c
  apply htime.congr_deriv
  rw [hdf, hdd.deriv]
  field_simp [hc, ne_of_gt (hpos x)]
  ring

def varianceLogHeat (c t : ℝ) (f : ℝ → ℝ) (x : ℝ) :=
  if c = 0 then varianceHeat t f x else Real.log (varianceHeat t (fun z => Real.exp (c*f z)) x)/c

lemma varianceLogHeat_eq_logSemigroup {f : ℝ → ℝ} (hfm : Measurable f) (c : ℝ)
    (h : ℝ≥0) (x : ℝ) : varianceLogHeat c h f x = logSemigroup c h f x := by
  by_cases hc : c = 0
  · simp only [varianceLogHeat, logSemigroup, hc, ↓reduceIte]
    exact varianceHeat_eq_semigroup hfm h x
  · simp only [varianceLogHeat, logSemigroup, hc, ↓reduceIte]
    have hem : Measurable (fun z => Real.exp (c*f z)) := (measurable_const.mul hfm).exp
    rw [varianceHeat_eq_semigroup hem h x]

lemma varianceHeat_exp_pos {f : ℝ → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    (c t x : ℝ) : 0 < varianceHeat t (fun z => Real.exp (c*f z)) x := by
  unfold varianceHeat scaled
  exact integral_pos_iff_support_of_nonneg (fun y => (Real.exp_pos _).le)
    (integrable_scaled_of_expBound (measurable_const.mul hf.continuous.measurable |>.exp)
      (exponentialBound_exp hf c) (Real.sqrt t) x) |>.mpr (by simp [Function.support])

lemma varianceLogHeat_equation {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) (c : ℝ) {t : ℝ} (ht : 0 ≤ t) (x : ℝ) :
    HasDerivWithinAt (fun s => varianceLogHeat c s f x)
      ((1/2:ℝ)*deriv (deriv (varianceLogHeat c t f)) x +
        c/2*(deriv (varianceLogHeat c t f) x)^2) (Set.Ici 0) t := by
  by_cases hc : c = 0
  · subst c
    have he : (fun s => varianceLogHeat 0 s f x) = fun s => varianceHeat s f x := by
      funext s; simp [varianceLogHeat]
    have he' : varianceLogHeat 0 t f = varianceHeat t f := by funext z; simp [varianceLogHeat]
    rw [he, he']
    simp only [zero_div, zero_mul, add_zero]
    obtain ⟨C,hC⟩ := hf.deriv_bounded.bound
    obtain ⟨C',hC'⟩ := hf.deriv_bounded.deriv.bound
    exact varianceHeat_equation (hf.smooth.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) (exponentialBound_of_lipschitz hLip)
      (ExponentialBound.of_bounded hC) (ExponentialBound.of_bounded hC') ht x
  · have he : (fun s => varianceLogHeat c s f x) = fun s =>
        Real.log (varianceHeat s (fun z => Real.exp (c*f z)) x)/c := by funext s; simp [varianceLogHeat, hc]
    have he' : varianceLogHeat c t f = fun z =>
        Real.log (varianceHeat t (fun y => Real.exp (c*f y)) z)/c := by funext z; simp [varianceLogHeat, hc]
    rw [he, he']
    exact logarithmic_heat_equation ((contDiff_const.mul hf.smooth).exp.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
      (exponentialBound_exp hLip c)
      (by simpa only [iteratedDeriv_one] using exponentialBound_exp_iteratedDeriv hf hLip c 1)
      (by simpa only [iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_zero] using exponentialBound_exp_iteratedDeriv hf hLip c 2)
      hc ht (varianceHeat_exp_pos hLip c t) x

end ZeroTemperatureSK.Heat

end
end
end
end

end OAI
