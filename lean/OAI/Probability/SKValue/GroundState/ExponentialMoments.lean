import Mathlib
import OAI.Probability.SKValue.Evolution.BoundedSmooth

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal
namespace SKValueG

instance expOneProbability : IsProbabilityMeasure (expMeasure 1) :=
  isProbabilityMeasure_expMeasure (by norm_num)

instance expOneNoAtoms : NullSingletonClass (expMeasure 1) := by
  unfold expMeasure gammaMeasure
  infer_instance

lemma exp_one_density_real (x : ℝ) :
    (gammaPDF 1 1 x).toReal = if 0 ≤ x then Real.exp (-x) else 0 := by
  simp only [gammaPDF,gammaPDFReal,Real.Gamma_one,Real.one_rpow,div_one,
    sub_self,Real.rpow_zero,mul_one,one_mul]
  rw [ENNReal.toReal_ofReal]
  split_ifs <;> positivity

lemma exp_one_pos_ae : ∀ᵐ x ∂expMeasure 1, 0<x := by
  have h : (expMeasure 1) (Iic 0)=0 := by
    have hc := cdf_expMeasure_eq (show (0 : ℝ)<1 by norm_num) 0
    rw [cdf_eq_real] at hc
    simpa [measureReal_def,ENNReal.toReal_eq_zero_iff,measure_ne_top] using hc
  rw [ae_iff]
  simpa only [not_lt, Iic] using h

lemma exp_one_integrable_iff (f : ℝ → ℝ) :
    Integrable f (expMeasure 1) ↔
      IntegrableOn (fun x ↦ Real.exp (-x)*f x) (Ioi 0) := by
  unfold expMeasure gammaMeasure
  rw [integrable_withDensity_iff_integrable_smul'
    (by unfold gammaPDF; fun_prop) (Eventually.of_forall (fun x ↦ by simp [gammaPDF]))]
  simp only [exp_one_density_real,smul_eq_mul]
  have he : (fun x ↦ (if 0 ≤ x then Real.exp (-x) else 0)*f x)=
      (Ici 0).indicator (fun x ↦ Real.exp (-x)*f x) := by
    ext x; by_cases h : 0≤x <;> simp [h]
  rw [he,integrable_indicator_iff measurableSet_Ici]
  exact integrableOn_Ici_iff_integrableOn_Ioi

lemma exp_one_rpow_integrable {p : ℝ} (hp : -1<p) :
    Integrable (fun x : ℝ ↦ x^p) (expMeasure 1) := by
  apply (exp_one_integrable_iff _).mpr
  have h := Real.GammaIntegral_convergent (s := p+1) (by linarith)
  simpa only [add_sub_cancel_right] using h

lemma abs_log_le_two_rpow {x : ℝ} (hx : 0<x) :
    |Real.log x| ≤ 2*(x^(1/2 : ℝ)+x^(-1/2 : ℝ)) := by
  have h1 := Real.log_le_rpow_div hx.le (show (0 : ℝ)<1/2 by norm_num)
  have h2 := Real.log_le_rpow_div (inv_nonneg.mpr hx.le) (show (0 : ℝ)<1/2 by norm_num)
  rw [Real.log_inv,Real.inv_rpow hx.le] at h2
  have he : (x^(1/2 : ℝ))⁻¹=x^(-1/2 : ℝ) := by
    rw [show (-1/2 : ℝ)=-(1/2 : ℝ) by ring,Real.rpow_neg hx.le]
  rw [he] at h2
  have hp1 := Real.rpow_nonneg hx.le (1/2 : ℝ)
  have hp2 := Real.rpow_nonneg hx.le (-1/2 : ℝ)
  apply abs_le.mpr
  constructor <;> linarith

lemma exp_one_log_integrable : Integrable Real.log (expMeasure 1) := by
  have h := ((exp_one_rpow_integrable (p := (1/2 : ℝ)) (by norm_num)).add
    (exp_one_rpow_integrable (p := (-1/2 : ℝ)) (by norm_num))).const_mul 2
  apply h.mono' Real.measurable_log.aestronglyMeasurable
  exact exp_one_pos_ae.mono (fun x hx ↦ by simpa only [Real.norm_eq_abs,Pi.add_apply] using abs_log_le_two_rpow hx)

end SKValueG

end

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal
namespace SKValueG

noncomputable def gumbelLaw : Measure ℝ := (expMeasure 1).map (fun x ↦ -Real.log x)

instance gumbelProbability : IsProbabilityMeasure gumbelLaw := by
  unfold gumbelLaw
  infer_instance

lemma gumbel_cdf (t : ℝ) : cdf gumbelLaw t=Real.exp (-Real.exp (-t)) := by
  rw [cdf_eq_real,gumbelLaw,measureReal_def,Measure.map_apply (by fun_prop) measurableSet_Iic]
  have he : (fun x ↦ -Real.log x) ⁻¹' Iic t =ᵐ[expMeasure 1] Ici (Real.exp (-t)) := by
    filter_upwards [exp_one_pos_ae] with x hx
    apply propext
    change -Real.log x ≤ t ↔ Real.exp (-t) ≤ x
    rw [←Real.le_log_iff_exp_le hx]
    constructor <;> intro h <;> linarith
  rw [measure_congr he,←measureReal_def,←compl_Iio,measureReal_compl measurableSet_Iio,
    measureReal_congr Iio_ae_eq_Iic,←cdf_eq_real,cdf_expMeasure_eq (by norm_num)]
  simp [Real.exp_nonneg,probReal_univ]

lemma gumbel_integrable : Integrable (fun x : ℝ ↦ x) gumbelLaw := by
  rw [gumbelLaw,integrable_map_measure (by fun_prop) (by fun_prop)]
  exact exp_one_log_integrable.neg

lemma gumbel_exp_integrable {p : ℝ} (hp : p<1) :
    Integrable (fun x : ℝ ↦ Real.exp (p*x)) gumbelLaw := by
  rw [gumbelLaw,integrable_map_measure (by fun_prop) (by fun_prop)]
  apply (exp_one_rpow_integrable (p := -p) (by linarith)).congr
  filter_upwards [exp_one_pos_ae] with x hx
  rw [Real.rpow_def_of_pos hx]
  congr 1
  ring

noncomputable def gumbelMean : ℝ := ∫ x, x ∂gumbelLaw

lemma prob_measure_eq_of_cdf {μ ν : Measure ℝ} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (h : ∀ t, cdf μ t=cdf ν t) : μ=ν := by
  apply Measure.ext_of_Iic
  intro t
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  exact (cdf_eq_real μ t).symm.trans ((h t).trans (cdf_eq_real ν t))

end SKValueG

end

end OAI
