import Mathlib
import OAI.Probability.SKValue.Evolution.ColeHopf

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators ContDiff
namespace SKValue

def ExpGrowth (f : ℝ → ℝ) : Prop :=
  ∃ a C : ℝ, 0≤a ∧ 0≤C ∧ ∀ x, |f x|≤C*Real.exp (a* |x|)

lemma gaussian_abs_mul_exp_integrable (a : ℝ) :
    Integrable (fun z ↦ |z| * Real.exp (a* |z|)) standardGaussian := by
  apply (gaussian_exp_abs_integrable (a+1)).mono' (by fun_prop)
  filter_upwards [] with z
  rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  calc
    _ ≤ Real.exp |z| * Real.exp (a* |z|) :=
      mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp |z|]) (Real.exp_pos _).le
    _ = Real.exp ((a+1)* |z|) := by rw [←Real.exp_add]; congr 1; ring

lemma expGrowth_shift_bound {f : ℝ → ℝ} {a C : ℝ} (ha : 0≤a) (hC : 0≤C)
    (hf : ∀ y, |f y|≤C*Real.exp (a* |y|)) (x s z : ℝ) :
    |f (x+s*z)|≤(C*Real.exp (a* |x|))*Real.exp ((a* |s|)* |z|) := by
  apply (hf _).trans
  rw [mul_assoc,←Real.exp_add]
  apply mul_le_mul_of_nonneg_left _ hC
  apply Real.exp_le_exp.mpr
  have hh := abs_add_le x (s*z)
  rw [abs_mul] at hh
  nlinarith

lemma ExpGrowth.shift_integrable {f : ℝ → ℝ} (hf : ExpGrowth f)
    (hm : Measurable f) (x s : ℝ) :
    Integrable (fun z ↦ f (x+s*z)) standardGaussian := by
  obtain ⟨a,C,ha,hC,hf⟩ := hf
  apply ((gaussian_exp_abs_integrable (a* |s|)).const_mul (C*Real.exp (a* |x|))).mono' ((hm.comp (by fun_prop)).aestronglyMeasurable)
  exact Eventually.of_forall (fun z ↦ (Real.norm_eq_abs _).trans_le (expGrowth_shift_bound ha hC hf x s z))

lemma ExpGrowth.shift_mul_integrable {f : ℝ → ℝ} (hf : ExpGrowth f)
    (hm : Measurable f) (x s : ℝ) :
    Integrable (fun z ↦ z*f (x+s*z)) standardGaussian := by
  obtain ⟨a,C,ha,hC,hf⟩ := hf
  apply ((gaussian_abs_mul_exp_integrable (a* |s|)).const_mul (C*Real.exp (a* |x|))).mono' (by exact (measurable_id.mul (hm.comp (by fun_prop))).aestronglyMeasurable)
  filter_upwards [] with z
  rw [Real.norm_eq_abs,abs_mul]
  simpa only [mul_assoc, mul_left_comm] using
    mul_le_mul_of_nonneg_left (expGrowth_shift_bound ha hC hf x s z) (abs_nonneg z)

lemma gaussian_shift_hasDerivAt {f f' : ℝ → ℝ} (hf : ∀ y, HasDerivAt f (f' y) y)
    (hf' : Continuous f') (hfg : ExpGrowth f) (hf'g : ExpGrowth f') (x s : ℝ) :
    HasDerivAt (fun y ↦ ∫ z, f (y+s*z) ∂standardGaussian)
      (∫ z, f' (x+s*z) ∂standardGaussian) x := by
  have hfc : Continuous f := continuous_iff_continuousAt.mpr (fun y ↦ (hf y).continuousAt)
  obtain ⟨a,C,ha,hC,hg⟩ := hf'g
  let bd := fun z ↦ (C*Real.exp (a*(|x|+1)))*Real.exp ((a* |s|)* |z|)
  have hbi : Integrable bd standardGaussian :=
    (gaussian_exp_abs_integrable (a* |s|)).const_mul _
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun y z ↦ f (y+s*z)) (F' := fun y z ↦ f' (y+s*z))
    (s := Metric.ball x 1) (bound := bd) (Metric.ball_mem_nhds x (by norm_num))
    (Eventually.of_forall (fun _ ↦ by fun_prop)) (hfg.shift_integrable hfc.measurable x s)
    (by fun_prop) _ hbi _).2
  · filter_upwards [] with z
    intro y hy
    have hyd : |y-x|≤1 := by simpa only [Metric.mem_ball,Real.dist_eq] using hy.le
    have hab : |y|≤|x|+1 := by
      have hh := abs_add_le (y-x) x
      rw [sub_add_cancel] at hh
      linarith
    rw [Real.norm_eq_abs]
    apply (expGrowth_shift_bound ha hC hg y s z).trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hab ha)) hC)
      (Real.exp_pos _).le
  · filter_upwards [] with z
    intro y _
    simpa only [Function.comp_def,id_eq,mul_one] using
      ((hf (y+s*z)).comp y ((hasDerivAt_id y).add_const (s*z)))

lemma gaussian_scale_hasDerivAt {f f' : ℝ → ℝ} (hf : ∀ y, HasDerivAt f (f' y) y)
    (hf' : Continuous f') (hfg : ExpGrowth f) (hf'g : ExpGrowth f') (x s : ℝ) :
    HasDerivAt (fun r ↦ ∫ z, f (x+r*z) ∂standardGaussian)
      (∫ z, z*f' (x+s*z) ∂standardGaussian) s := by
  have hfc : Continuous f := continuous_iff_continuousAt.mpr (fun y ↦ (hf y).continuousAt)
  obtain ⟨a,C,ha,hC,hg⟩ := hf'g
  let bd := fun z ↦ (C*Real.exp (a* |x|))*(|z| * Real.exp ((a*(|s|+1))* |z|))
  have hbi : Integrable bd standardGaussian :=
    (gaussian_abs_mul_exp_integrable (a*(|s|+1))).const_mul _
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun r z ↦ f (x+r*z)) (F' := fun r z ↦ z*f' (x+r*z))
    (s := Metric.ball s 1) (bound := bd) (Metric.ball_mem_nhds s (by norm_num))
    (Eventually.of_forall (fun _ ↦ by fun_prop)) (hfg.shift_integrable hfc.measurable x s)
    (by fun_prop) _ hbi _).2
  · filter_upwards [] with z
    intro r hr
    have hrd : |r-s|≤1 := by simpa only [Metric.mem_ball,Real.dist_eq] using hr.le
    have hab : |r|≤|s|+1 := by
      have hh := abs_add_le (r-s) s
      rw [sub_add_cancel] at hh
      linarith
    rw [Real.norm_eq_abs,abs_mul]
    apply (mul_le_mul_of_nonneg_left (expGrowth_shift_bound ha hC hg x r z) (abs_nonneg z)).trans
    have hex : Real.exp ((a* |r|)* |z|)≤Real.exp ((a*(|s|+1))* |z|) := by
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hab ha) (abs_nonneg z))
    have hh := mul_le_mul_of_nonneg_left hex (by positivity : 0≤|z| * (C*Real.exp (a* |x|)))
    dsimp only [bd]
    nlinarith
  · filter_upwards [] with z
    intro r _
    have hh := (hf (x+r*z)).comp r (((hasDerivAt_id r).mul_const z).const_add x)
    simpa only [Function.comp_def,id_eq,one_mul,mul_one,mul_comm] using hh

lemma gaussian_scale_deriv_eq {f f' : ℝ → ℝ}
    (hf : ∀ y, HasDerivAt f (f' y) y) (hf' : Continuous f')
    (hfg : ExpGrowth f) (hf'g : ExpGrowth f') (x s : ℝ) :
    (∫ z, z*f (x+s*z) ∂standardGaussian) = s*(∫ z, f' (x+s*z) ∂standardGaussian) := by
  have hfc : Continuous f := continuous_iff_continuousAt.mpr (fun y ↦ (hf y).continuousAt)
  have hh := gaussian_stein_of_integrable
    (f := fun z ↦ f (x+s*z)) (f' := fun z ↦ s*f' (x+s*z))
    (fun z ↦ by
      have hd := (hf (x+s*z)).comp z (((hasDerivAt_id z).const_mul s).const_add x)
      simpa only [Function.comp_def,id_eq,mul_one,mul_comm] using hd)
    (hfg.shift_integrable hfc.measurable x s)
    ((hf'g.shift_integrable hf'.measurable x s).const_mul s)
    (hfg.shift_mul_integrable hfc.measurable x s)
  simpa only [integral_const_mul] using hh

lemma heat_time_hasDerivAt {f f' f'' : ℝ → ℝ}
    (hf : ∀ y, HasDerivAt f (f' y) y) (hf' : ∀ y, HasDerivAt f' (f'' y) y)
    (hf'' : Continuous f'') (hfg : ExpGrowth f) (hf'g : ExpGrowth f')
    (hf''g : ExpGrowth f'') (x : ℝ) {h : ℝ} (hh : 0<h) :
    HasDerivAt (fun r ↦ heat r f x) ((1/2 : ℝ)*heat h f'' x) h := by
  have hf'c : Continuous f' := continuous_iff_continuousAt.mpr (fun y ↦ (hf' y).continuousAt)
  have hd := (gaussian_scale_hasDerivAt hf hf'c hfg hf'g x (Real.sqrt h)).comp h
    (Real.hasDerivAt_sqrt hh.ne')
  rw [gaussian_scale_deriv_eq hf' hf'' hf'g hf''g x (Real.sqrt h)] at hd
  convert! hd using 1
  dsimp only [heat]
  field_simp [Real.sqrt_ne_zero'.mpr hh]

lemma heat_spatial_hasDerivAt {f f' : ℝ → ℝ}
    (hf : ∀ y, HasDerivAt f (f' y) y) (hf' : Continuous f')
    (hfg : ExpGrowth f) (hf'g : ExpGrowth f') (x h : ℝ) :
    HasDerivAt (heat h f) (heat h f' x) x :=
  gaussian_shift_hasDerivAt hf hf' hfg hf'g x (Real.sqrt h)

lemma heat_iteratedDeriv {f : ℝ → ℝ} (hf : ContDiff ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) f)
    (hg : ∀ n : ℕ, ExpGrowth (iteratedDeriv n f)) (h : ℝ) (n : ℕ) :
    iteratedDeriv n (heat h f) = heat h (iteratedDeriv n f) := by
  induction n with
  | zero => simp only [iteratedDeriv_zero]
  | succ n ih =>
    rw [iteratedDeriv_succ,ih]
    funext x
    exact (heat_spatial_hasDerivAt
      (fun y ↦ by simpa only [iteratedDeriv_succ] using
        ((hf.differentiable_iteratedDeriv n (ENat.natCast_lt_of_coe_top_le_withTop le_rfl n)) y).hasDerivAt)
      (hf.continuous_iteratedDeriv (n+1) (ENat.natCast_le_of_coe_top_le_withTop le_rfl (n+1))) (hg n) (hg (n+1)) x h).deriv

lemma heat_contDiff {f : ℝ → ℝ} (hf : ContDiff ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) f)
    (hg : ∀ n : ℕ, ExpGrowth (iteratedDeriv n f)) (h : ℝ) :
    ContDiff ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) (heat h f) := by
  apply contDiff_of_differentiable_iteratedDeriv (n := ⊤)
  intro n _
  rw [heat_iteratedDeriv hf hg]
  intro x
  exact (heat_spatial_hasDerivAt
    (fun y ↦ by simpa only [iteratedDeriv_succ] using
      ((hf.differentiable_iteratedDeriv n (ENat.natCast_lt_of_coe_top_le_withTop le_rfl n)) y).hasDerivAt)
    (hf.continuous_iteratedDeriv (n+1) (ENat.natCast_le_of_coe_top_le_withTop le_rfl (n+1))) (hg n) (hg (n+1)) x h).differentiableAt

end SKValue

end

end OAI
