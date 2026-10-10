import Mathlib
import OAI.Analysis.CoulombRadii.Packets.CoulombKernelFiveHalvesIntegrable

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb
noncomputable def gaussian (a : ℝ) (x : Space) : ℝ := Real.exp (-a*‖x‖^2)
lemma gaussian_pos (a : ℝ) (x : Space) : 0 < gaussian a x := Real.exp_pos _
lemma gaussian_le_one {a : ℝ} (ha : 0 ≤ a) (x : Space) : gaussian a x ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  nlinarith [sq_nonneg ‖x‖]
lemma gaussian_continuous (a : ℝ) : Continuous (gaussian a) := by unfold gaussian; fun_prop
lemma gaussian_integrable {a : ℝ} (ha : 0 < a) : Integrable (gaussian a) := by
  change Integrable (fun x : Space => Real.exp (-a*‖x‖^2))
  have H := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V:=Space)
    (show 0 < (a : ℂ).re from ha) 0 0).re
  change Integrable (fun x : Space => (Complex.exp (-(a:ℂ)*↑‖x‖^2 + 0 * ↑(inner ℝ (0:Space) x))).re) at H
  simpa only [zero_mul, add_zero, ← Complex.ofReal_pow, ← Complex.ofReal_neg,
    ← Complex.ofReal_mul, ← Complex.ofReal_exp, Complex.ofReal_re, gaussian] using H
lemma gaussian_integral {a : ℝ} (ha : 0 < a) :
    (∫ x, gaussian a x) = (Real.pi/a)^(3/2:ℝ) := by
  simpa [gaussian] using GaussianFourier.integral_rexp_neg_mul_sq_norm (V:=Space) ha
lemma kernel_gaussian_integral {d : Space} (hd : d ≠ 0) :
    ‖d‖⁻¹ = (Real.sqrt Real.pi)⁻¹ * ∫ t : ℝ, gaussian (t^2) d := by
  have he (t : ℝ) : gaussian (t^2) d = Real.exp (-(‖d‖^2)*t^2) := by
    unfold gaussian
    congr 1
    ring
  simp_rw [he]
  rw [integral_gaussian, Real.sqrt_div (by positivity), Real.sqrt_sq (norm_nonneg _)]
  field_simp

lemma gaussian_product (a : ℝ) (x y z : Space) :
    gaussian (2*a) (x-z)*gaussian (2*a) (y-z) =
      gaussian a (x-y)*gaussian (4*a) (z-(1/2:ℝ) • (x+y)) := by
  unfold gaussian
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  simp only [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0:ℝ) < 1/2),
    inner_smul_right, inner_add_right]
  rw [mul_pow, norm_add_sq_real]
  rw [real_inner_comm z x, real_inner_comm z y]
  ring

lemma gaussian_product_integrable {a : ℝ} (ha : 0 < a) (x y : Space) :
    Integrable (fun z => gaussian (2*a) (x-z)*gaussian (2*a) (y-z)) := by
  simp_rw [gaussian_product]
  exact ((gaussian_integrable (by positivity : 0 < 4*a)).comp_sub_right _).const_mul _

lemma gaussian_convolution_identity {a : ℝ} (ha : 0 < a) (x y : Space) :
    (∫ z, gaussian (2*a) (x-z)*gaussian (2*a) (y-z)) =
      gaussian a (x-y)*(Real.pi/(4*a))^(3/2:ℝ) := by
  simp_rw [gaussian_product]
  rw [integral_const_mul, integral_sub_right_eq_self, gaussian_integral (by positivity)]

lemma integrable_gaussian_weight {f : Space → ℝ} (hf : Integrable f) (hm : Measurable f)
    {a : ℝ} (ha : 0 ≤ a) (z : Space) :
    Integrable (fun x => f x * gaussian a (x-z)) := by
  apply hf.norm.mono' (hm.mul ((gaussian_continuous a).measurable.comp (by fun_prop))).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x => by
    change ‖f x * gaussian a (x-z)‖ ≤ ‖f x‖
    rw [norm_mul, Real.norm_of_nonneg (gaussian_pos a _).le]
    exact mul_le_of_le_one_right (norm_nonneg _) (gaussian_le_one ha _))

lemma integrable_gaussian_pair {f : Space → ℝ} (hf : Integrable f) (hm : Measurable f)
    {a : ℝ} (ha : 0 ≤ a) :
    Integrable (fun p : Space × Space => f p.1*f p.2*gaussian a (p.1-p.2)) := by
  apply (hf.norm.mul_prod hf.norm).mono' (by
    apply Measurable.aestronglyMeasurable
    exact ((hm.comp measurable_fst).mul (hm.comp measurable_snd)).mul
      ((gaussian_continuous a).measurable.comp (by fun_prop)))
  exact Filter.Eventually.of_forall (fun p => by
    simp only [norm_mul, Real.norm_of_nonneg (gaussian_pos a _).le]
    exact mul_le_of_le_one_right (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (gaussian_le_one ha _))

lemma gaussian_square_integrable {f : Space → ℝ} (hf : Integrable f) (hm : Measurable f)
    {a : ℝ} (ha : 0 < a) :
    Integrable (fun q : (Space × Space) × Space =>
      (f q.1.1*f q.1.2)*(gaussian (2*a) (q.1.1-q.2)*gaussian (2*a) (q.1.2-q.2))) := by
  have hm' : Measurable (fun q : (Space × Space) × Space =>
      (f q.1.1*f q.1.2)*(gaussian (2*a) (q.1.1-q.2)*gaussian (2*a) (q.1.2-q.2))) := by
    have h1 : Measurable (fun q : (Space × Space) × Space => f q.1.1*f q.1.2) :=
      (hm.comp (by fun_prop)).mul (hm.comp (by fun_prop))
    apply h1.mul
    exact ((gaussian_continuous _).measurable.comp (by fun_prop)).mul
      ((gaussian_continuous _).measurable.comp (by fun_prop))
  apply (integrable_prod_iff hm'.aestronglyMeasurable).mpr
  constructor
  · exact Filter.Eventually.of_forall (fun p => (gaussian_product_integrable ha p.1 p.2).const_mul (f p.1*f p.2))
  · have he (p : Space × Space) :
        (∫ z, ‖(f p.1*f p.2)*(gaussian (2*a) (p.1-z)*gaussian (2*a) (p.2-z))‖) =
          (‖f p.1‖*‖f p.2‖*gaussian a (p.1-p.2))*(Real.pi/(4*a))^(3/2:ℝ) := by
      simp_rw [norm_mul, Real.norm_of_nonneg (gaussian_pos ..).le]
      rw [integral_const_mul, gaussian_convolution_identity ha]
      ring
    simp_rw [he]
    exact (integrable_gaussian_pair hf.norm hm.norm ha.le).mul_const _

lemma gaussian_form_nonneg {f : Space → ℝ} (hf : Integrable f) (hm : Measurable f)
    {a : ℝ} (ha : 0 < a) :
    0 ≤ ∫ p : Space × Space, f p.1*f p.2*gaussian a (p.1-p.2) := by
  have hi := gaussian_square_integrable hf hm ha
  have H := integral_integral_swap (f := fun (p : Space × Space) (z : Space) =>
    (f p.1*f p.2)*(gaussian (2*a) (p.1-z)*gaussian (2*a) (p.2-z))) hi
  have hleft (p : Space × Space) :
      (∫ z, (f p.1*f p.2)*(gaussian (2*a) (p.1-z)*gaussian (2*a) (p.2-z))) =
        (f p.1*f p.2*gaussian a (p.1-p.2))*(Real.pi/(4*a))^(3/2:ℝ) := by
    rw [integral_const_mul, gaussian_convolution_identity ha]
    ring
  have hright (z : Space) :
      (∫ p : Space × Space, (f p.1*f p.2)*(gaussian (2*a) (p.1-z)*gaussian (2*a) (p.2-z))) =
        (∫ x, f x*gaussian (2*a) (x-z))^2 := by
    simp_rw [show ∀ p : Space × Space,
      (f p.1*f p.2)*(gaussian (2*a) (p.1-z)*gaussian (2*a) (p.2-z)) =
      (f p.1*gaussian (2*a) (p.1-z))*(f p.2*gaussian (2*a) (p.2-z)) from fun p => by ring]
    exact (integral_prod_mul (μ:=volume) (ν:=volume)
      (fun x : Space => f x*gaussian (2*a) (x-z))
      (fun x : Space => f x*gaussian (2*a) (x-z))).trans (pow_two _).symm
  simp_rw [hleft, hright] at H
  rw [integral_mul_const] at H
  have hnonneg : 0 ≤ (∫ p : Space × Space, f p.1*f p.2*gaussian a (p.1-p.2)) *
      (Real.pi/(4*a))^(3/2:ℝ) := H.symm ▸ integral_nonneg (fun z => sq_nonneg _)
  exact nonneg_of_mul_nonneg_left hnonneg (Real.rpow_pos_of_pos (by positivity) _)
lemma space_ae_distinct : ∀ᵐ p : Space × Space, p.1 ≠ p.2 := by
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun measurable_fst measurable_snd).compl).mpr
  exact Filter.Eventually.of_forall (fun x => by
    rw [ae_iff]
    simp only [not_not]
    have he : {y : Space | x = y} = {x} := by ext y; simp [eq_comm]
    change volume {y : Space | x = y} = 0
    rw [he, measure_singleton])

lemma gaussian_parameter_integrable {d : Space} (hd : d ≠ 0) :
    Integrable (fun t : ℝ => gaussian (t^2) d) := by
  have he (t : ℝ) : gaussian (t^2) d = Real.exp (-(‖d‖^2)*t^2) := by
    unfold gaussian
    congr 1
    ring
  simp_rw [he]
  exact integrable_exp_neg_mul_sq (sq_pos_of_pos (norm_pos_iff.mpr hd))

lemma gaussian_parameter_integral {d : Space} (hd : d ≠ 0) :
    (∫ t : ℝ, gaussian (t^2) d) = coulombKernel d * Real.sqrt Real.pi := by
  have H := kernel_gaussian_integral hd
  unfold coulombKernel
  have hp : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  calc
    _ = ((Real.sqrt Real.pi)⁻¹*(∫ t : ℝ, gaussian (t^2) d))*Real.sqrt Real.pi := by field_simp
    _ = _ := by rw [← H]

lemma coulomb_gaussian_integrable_of_pair {f : Space → ℝ} (hm : Measurable f)
    (hp : Integrable (fun p : Space × Space => f p.1*f p.2*coulombKernel (p.1-p.2))) :
    Integrable (fun q : (Space × Space) × ℝ =>
      (f q.1.1*f q.1.2)*gaussian (q.2^2) (q.1.1-q.1.2)) := by
  have hm' : Measurable (fun q : (Space × Space) × ℝ =>
      (f q.1.1*f q.1.2)*gaussian (q.2^2) (q.1.1-q.1.2)) := by
    apply ((hm.comp (by fun_prop)).mul (hm.comp (by fun_prop))).mul
    unfold gaussian
    fun_prop
  apply (integrable_prod_iff hm'.aestronglyMeasurable).mpr
  constructor
  · filter_upwards [space_ae_distinct] with p hp
    exact (gaussian_parameter_integrable (sub_ne_zero.mpr hp)).const_mul (f p.1*f p.2)
  · have hi := hp.norm.mul_const (Real.sqrt Real.pi)
    apply hi.congr
    filter_upwards [space_ae_distinct] with p hp
    simp_rw [norm_mul, Real.norm_of_nonneg (gaussian_pos ..).le]
    rw [integral_const_mul, gaussian_parameter_integral (sub_ne_zero.mpr hp)]
    simp only [Real.norm_of_nonneg (coulombKernel_nonneg _)]
    ring

lemma coulomb_form_nonneg_of_pair {f : Space → ℝ} (hf : Integrable f) (hm : Measurable f)
    (hp : Integrable (fun p : Space × Space => f p.1*f p.2*coulombKernel (p.1-p.2))) :
    0 ≤ ∫ p : Space × Space, f p.1*f p.2*coulombKernel (p.1-p.2) := by
  have hi := coulomb_gaussian_integrable_of_pair hm hp
  have H := integral_integral_swap (f := fun (p : Space × Space) (t : ℝ) =>
    f p.1*f p.2*gaussian (t^2) (p.1-p.2)) hi
  have hl : (∫ p : Space × Space, ∫ t : ℝ, f p.1*f p.2*gaussian (t^2) (p.1-p.2)) =
      (∫ p : Space × Space, f p.1*f p.2*coulombKernel (p.1-p.2))*Real.sqrt Real.pi := by
    rw [← integral_mul_const]
    apply integral_congr_ae
    filter_upwards [space_ae_distinct] with p hp
    rw [integral_const_mul, gaussian_parameter_integral (sub_ne_zero.mpr hp)]
    ring
  rw [hl] at H
  have ht : ∀ᵐ t : ℝ, t ≠ 0 := by rw [ae_iff]; simp
  have hn : 0 ≤ ∫ t : ℝ, ∫ p : Space × Space, f p.1*f p.2*gaussian (t^2) (p.1-p.2) := by
    apply integral_nonneg_of_ae
    filter_upwards [ht] with t ht
    exact gaussian_form_nonneg hf hm (sq_pos_of_ne_zero ht)
  rw [← H] at hn
  exact nonneg_of_mul_nonneg_left hn (Real.sqrt_pos.mpr Real.pi_pos)

lemma coulomb_lp_form_nonneg {f : Space → ℝ} (hf : Integrable f) (hm : Measurable f)
    (hp : MemLp f (ENNReal.ofReal (5/3:ℝ)) volume) :
    0 ≤ ∫ p : Space × Space, f p.1*f p.2*coulombKernel (p.1-p.2) :=
  coulomb_form_nonneg_of_pair hf hm (coulomb_lp_pair_integrable hf hm hf hm hp)
end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

end
end

end OAI
