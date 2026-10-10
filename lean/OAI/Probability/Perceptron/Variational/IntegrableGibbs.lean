import Mathlib
import OAI.Probability.Perceptron.Variational.StableLaplaceConstant

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

section
variable {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]

lemma tilt_partition_pos_of_integrable {H : S → ℝ} {t : ℝ}
    (hi : Integrable (fun x => Real.exp (t*H x)) μ) : 0 < tiltPartition μ H t := by
  unfold tiltPartition
  apply (integral_pos_iff_support_of_nonneg (fun _ => (Real.exp_pos _).le) hi).mpr
  have he : Function.support (fun x => Real.exp (t*H x)) = univ := by
    ext x
    simp only [Function.mem_support,ne_eq,mem_univ]
    exact iff_of_true (Real.exp_pos _).ne' trivial
  rw [he,measure_univ]
  exact zero_lt_one

lemma tilt_law_probability_of_integrable {H : S → ℝ} {t : ℝ}
    (hi : Integrable (fun x => Real.exp (t*H x)) μ) :
    IsProbabilityMeasure (tiltLaw μ H t) := by
  have hp := tilt_partition_pos_of_integrable μ hi
  constructor
  rw [tiltLaw,Measure.smul_apply,smul_eq_mul,withDensity_apply _ .univ,
    Measure.restrict_univ,← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun x => (Real.exp_pos _).le)]
  exact ENNReal.inv_mul_cancel (ne_of_gt (ENNReal.ofReal_pos.mpr hp)) ENNReal.ofReal_ne_top

lemma tilt_law_integral_of_integrable {H F : S → ℝ} (hH : Measurable H) {t : ℝ}
    (hi : Integrable (fun x => Real.exp (t*H x)) μ) :
    (∫ x, F x ∂tiltLaw μ H t)=tiltMean μ H F t := by
  rw [tiltLaw,integral_smul_measure,integral_withDensity_eq_integral_toReal_smul
    (hH.const_mul t).exp.ennreal_ofReal (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_inv,ENNReal.toReal_ofReal (tilt_partition_pos_of_integrable μ hi).le,
    ENNReal.toReal_ofReal (Real.exp_pos _).le,smul_eq_mul,tiltMean,tiltIntegral]
  exact (div_eq_inv_mul _ _).symm

lemma tiltMean_bound_of_integrable {H F : S → ℝ} (hH : Measurable H) (_hF : Measurable F)
    {t C : ℝ} (hi : Integrable (fun x => Real.exp (t*H x)) μ)
    (hC : ∀ x, |F x| ≤ C) : |tiltMean μ H F t| ≤ C := by
  let := tilt_law_probability_of_integrable μ hi
  rw [← tilt_law_integral_of_integrable μ hH hi]
  have hh := norm_integral_le_of_norm_le_const (μ := tiltLaw μ H t) (f := F)
    (C := C) (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hC x)
  simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using hh

lemma exp_integral_le_of_integrable {H : S → ℝ} (hi : Integrable H μ)
    (he : Integrable (fun x => Real.exp (H x)) μ) :
    Real.exp (∫ x, H x ∂μ) ≤ ∫ x, Real.exp (H x) ∂μ := by
  exact convexOn_exp.map_integral_le Real.continuous_exp.continuousOn isClosed_univ
    (ae_of_all _ fun _ => mem_univ _) hi he

lemma inverse_partition_power_le {H : S → ℝ} (hi : Integrable H μ)
    (he : Integrable (fun x => Real.exp (H x)) μ) (k : ℕ)
    (hk : Integrable (fun x => Real.exp (-(k:ℝ)*H x)) μ) :
    (tiltPartition μ H 1)⁻¹^k ≤ ∫ x, Real.exp (-(k:ℝ)*H x) ∂μ := by
  have h1 : Real.exp (∫ x, H x ∂μ) ≤ tiltPartition μ H 1 := by
    simpa only [tiltPartition,one_mul] using exp_integral_le_of_integrable μ hi he
  have h2 : (tiltPartition μ H 1)⁻¹ ≤ (Real.exp (∫ x, H x ∂μ))⁻¹ :=
    inv_anti₀ (Real.exp_pos _) h1
  calc
    _ ≤ ((Real.exp (∫ x, H x ∂μ))⁻¹)^k :=
      pow_le_pow_left₀ (inv_nonneg.mpr (tilt_partition_pos_of_integrable μ (by simpa only [one_mul] using he)).le) h2 k
    _ = Real.exp (-(k:ℝ)*(∫ x, H x ∂μ)) := by
      rw [← Real.exp_neg,← Real.exp_nat_mul]
      congr 1
      ring
    _ = Real.exp (∫ x, -(k:ℝ)*H x ∂μ) := by rw [integral_const_mul]
    _ ≤ _ := exp_integral_le_of_integrable μ (hi.const_mul _) hk

end

lemma abs_le_exp_add_exp_neg (a : ℝ) : |a| ≤ Real.exp a+Real.exp (-a) := by
  by_cases ha : 0 ≤ a
  · rw [abs_of_nonneg ha]
    linarith [Real.add_one_le_exp a,Real.exp_pos (-a)]
  · rw [abs_of_neg (lt_of_not_ge ha)]
    linarith [Real.add_one_le_exp (-a),Real.exp_pos a]

lemma abs_pow_mul_exp_le (h y : ℝ) (k : ℕ) :
    |y|^k*Real.exp h ≤ (k.factorial:ℝ)*(Real.exp (h+y)+Real.exp (h-y)) := by
  have hk : (0:ℝ)<k.factorial := by exact_mod_cast k.factorial_pos
  have h1 : |y|^k ≤ (k.factorial:ℝ)*Real.exp |y| := by
    have hh := Real.pow_div_factorial_le_exp |y| (abs_nonneg y) k
    exact (div_le_iff₀ hk).mp hh |>.trans_eq (mul_comm _ _)
  have h2 : Real.exp |y| ≤ Real.exp y+Real.exp (-y) := by
    by_cases hy : 0 ≤ y
    · rw [abs_of_nonneg hy]
      exact le_add_of_nonneg_right (Real.exp_pos _).le
    · rw [abs_of_neg (lt_of_not_ge hy)]
      exact le_add_of_nonneg_left (Real.exp_pos _).le
  calc
    _ ≤ ((k.factorial:ℝ)*(Real.exp y+Real.exp (-y)))*Real.exp h :=
      mul_le_mul_of_nonneg_right (h1.trans (mul_le_mul_of_nonneg_left h2 hk.le)) (Real.exp_pos _).le
    _ = _ := by
      rw [mul_assoc,add_mul,← Real.exp_add,← Real.exp_add]
      congr 1
      congr 1 <;> congr 1 <;> ring

lemma integrable_of_exp_pos_neg {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {H : X → ℝ} (hm : Measurable H)
    (hp : Integrable (fun x => Real.exp (H x)) μ)
    (hn : Integrable (fun x => Real.exp (-H x)) μ) : Integrable H μ := by
  apply (hp.add hn).mono' hm.aestronglyMeasurable
  exact ae_of_all _ fun x => by
    simpa only [Real.norm_eq_abs,Pi.add_apply] using abs_le_exp_add_exp_neg (H x)

variable {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
lemma coupling_mgf_identity {H Y : S → ℝ} (hH : Measurable H) (a : ℝ) :
    mgf Y (μ.withDensity (fun x => ENNReal.ofReal (Real.exp (H x)))) a =
      tiltPartition μ (fun x => H x+a*Y x) 1 := by
  rw [mgf,integral_withDensity_eq_integral_toReal_smul hH.exp.ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (Real.exp_pos _).le,smul_eq_mul,tiltPartition,one_mul,Real.exp_add]

omit [IsProbabilityMeasure μ] in
lemma coupling_expSet {H Y : S → ℝ} (hH : Measurable H) (_hY : Measurable Y)
    (he : ∀ a : ℝ, Integrable (fun x => Real.exp (H x+a*Y x)) μ) :
    integrableExpSet Y (μ.withDensity (fun x => ENNReal.ofReal (Real.exp (H x)))) = univ := by
  ext a
  simp only [mem_univ,iff_true,integrableExpSet,mem_ofPred_eq]
  apply (integrable_withDensity_iff_integrable_smul' hH.exp.ennreal_ofReal (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)).mpr
  simpa only [ENNReal.toReal_ofReal (Real.exp_pos _).le,smul_eq_mul,Real.exp_add] using he a

lemma coupling_log_hasDerivAt {H Y : S → ℝ} (hH : Measurable H) (hY : Measurable Y)
    (he : ∀ a : ℝ, Integrable (fun x => Real.exp (H x+a*Y x)) μ) (a : ℝ) :
    HasDerivAt (fun b => Real.log (tiltPartition μ (fun x => H x+b*Y x) 1))
      (tiltMean μ (fun x => H x+a*Y x) Y 1) a := by
  let ρ := μ.withDensity (fun x => ENNReal.ofReal (Real.exp (H x)))
  have hm : a ∈ interior (integrableExpSet Y ρ) := by
    rw [coupling_expSet μ hH hY he,interior_univ]
    trivial
  have hp : 0 < mgf Y ρ a := by
    rw [coupling_mgf_identity μ hH]
    exact tilt_partition_pos_of_integrable μ (by simpa only [one_mul] using he a)
  have hd := (hasDerivAt_mgf hm).log hp.ne'
  have hf : (fun b => Real.log (mgf Y ρ b)) =
      (fun b => Real.log (tiltPartition μ (fun x => H x+b*Y x) 1)) := by
    funext b
    rw [coupling_mgf_identity μ hH]
  rw [hf] at hd
  convert hd using 1
  rw [coupling_mgf_identity μ hH]
  unfold tiltMean tiltIntegral
  congr 1
  change _ = ∫ x, Y x*Real.exp (a*Y x) ∂ρ
  rw [integral_withDensity_eq_integral_toReal_smul hH.exp.ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [ENNReal.toReal_ofReal (Real.exp_pos _).le,smul_eq_mul,one_mul,Real.exp_add]
  ring

lemma coupling_log_second_derivative {H Y : S → ℝ} (hH : Measurable H) (hY : Measurable Y)
    (he : ∀ a : ℝ, Integrable (fun x => Real.exp (H x+a*Y x)) μ) (a : ℝ) :
    iteratedDeriv 2 (fun b => Real.log (tiltPartition μ (fun x => H x+b*Y x) 1)) a =
      tiltMean μ (fun x => H x+a*Y x)
        (fun x => (Y x-tiltMean μ (fun x => H x+a*Y x) Y 1)^2) 1 := by
  let ρ := μ.withDensity (fun x => ENNReal.ofReal (Real.exp (H x)))
  have hm : a ∈ interior (integrableExpSet Y ρ) := by
    rw [coupling_expSet μ hH hY he,interior_univ]
    trivial
  have hf : cgf Y ρ = (fun b => Real.log (tiltPartition μ (fun x => H x+b*Y x) 1)) := by
    funext b
    exact congrArg Real.log (coupling_mgf_identity μ hH b)
  have hd : deriv (cgf Y ρ) a = tiltMean μ (fun x => H x+a*Y x) Y 1 := by
    rw [hf]
    exact (coupling_log_hasDerivAt μ hH hY he a).deriv
  rw [← hf,iteratedDeriv_two_cgf_eq_integral hm,hd,coupling_mgf_identity μ hH]
  unfold tiltMean tiltIntegral
  congr 1
  rw [integral_withDensity_eq_integral_toReal_smul hH.exp.ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [ENNReal.toReal_ofReal (Real.exp_pos _).le,smul_eq_mul,one_mul,Real.exp_add]
  ring

end SphericalPerceptronFreeEnergy

end

end OAI
