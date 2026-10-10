import Mathlib
import OAI.Probability.SKRatio.Variational.ScalarReduction

namespace OAI

noncomputable section
open scoped Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Real Set
namespace SKRatio.Scalar

lemma variance_ne_zero {β : ℝ} (hβ : 0 < β) : variance β ≠ 0 := by
  intro hz
  have he := congrArg (fun t : ℝ≥0 => (t:ℝ)) hz
  simp only [variance_coe,NNReal.coe_zero] at he
  nlinarith

lemma field_pdf {β : ℝ} (hβ : 0 < β) (h : ℝ) :
    gaussianPDFReal (β^2) (variance β) h =
      (sqrt (2*Real.pi)*β)⁻¹*exp (-β^2/2+h-h^2/(2*β^2)) := by
  unfold gaussianPDFReal
  rw [variance_coe,sqrt_mul (by positivity : 0 ≤ 2*Real.pi),sqrt_sq hβ.le]
  congr 2
  field_simp
  ring

lemma thermal_prefactor_deriv (β : ℝ) :
    HasDerivAt (fun t : ℝ => t*exp (-t^2/2))
      ((1-β^2)*exp (-β^2/2)) β := by
  convert! (hasDerivAt_id β).mul
    ((((hasDerivAt_id β).pow 2).neg.div_const 2).exp) using 1
  simp only [Nat.cast_ofNat,show 2-1=1 from rfl,pow_one,id_eq,Pi.neg_apply,Pi.pow_apply]
  ring

lemma thermal_prefactor_mono {β z : ℝ} (hβ : 0 ≤ β) (hβz : β ≤ z) (hz : z ≤ 1) :
    β*exp (-β^2/2) ≤ z*exp (-z^2/2) := by
  apply (monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc (0:ℝ) 1)
    (fun x _ => (thermal_prefactor_deriv x).continuousAt.continuousWithinAt)
    (fun x _ => (thermal_prefactor_deriv x).hasDerivWithinAt) ?_) ⟨hβ,le_trans hβz hz⟩ ⟨le_trans hβ hβz,hz⟩ hβz
  intro x hx
  have hx' : x ∈ Icc (0:ℝ) 1 := interior_subset hx
  exact mul_nonneg (by nlinarith [hx'.1,hx'.2]) (exp_pos _).le

lemma scaled_field_pdf {β : ℝ} (hβ : 0 < β) (h : ℝ) :
    β^2*gaussianPDFReal (β^2) (variance β) h =
      (sqrt (2*Real.pi))⁻¹*(β*exp (-β^2/2))*exp (h-h^2/(2*β^2)) := by
  rw [field_pdf hβ]
  have he : -β^2/2+h-h^2/(2*β^2) = -β^2/2+(h-h^2/(2*β^2)) := by ring
  rw [he,exp_add]
  field_simp

lemma scaled_field_pdf_mono {β z : ℝ} (hβ : 0 < β) (hβz : β ≤ z) (hz : z ≤ 1) (h : ℝ) :
    β^2*gaussianPDFReal (β^2) (variance β) h ≤
      z^2*gaussianPDFReal (z^2) (variance z) h := by
  have hzpos : 0 < z := lt_of_lt_of_le hβ hβz
  rw [scaled_field_pdf hβ,scaled_field_pdf hzpos]
  have hq : h^2/(2*z^2) ≤ h^2/(2*β^2) := by
    apply div_le_div_of_nonneg_left (sq_nonneg h) (by positivity)
    nlinarith
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_left (thermal_prefactor_mono hβ.le hβz hz) (by positivity)
  · exact exp_le_exp.mpr (by linarith only [hq])
  · exact (exp_pos _).le
  · positivity

theorem scaled_fieldLaw_mono {β z : ℝ} (hβ : 0 < β) (hβz : β ≤ z) (hz : z ≤ 1) :
    ENNReal.ofReal (β^2) • fieldLaw β ≤ ENNReal.ofReal (z^2) • fieldLaw z := by
  have hzpos : 0 < z := lt_of_lt_of_le hβ hβz
  rw [fieldLaw,fieldLaw,gaussianReal_of_var_ne_zero _ (variance_ne_zero hβ),
    gaussianReal_of_var_ne_zero _ (variance_ne_zero hzpos),
    ←withDensity_smul' _ _ ENNReal.ofReal_ne_top,←withDensity_smul' _ _ ENNReal.ofReal_ne_top]
  apply withDensity_mono
  apply ae_of_all
  intro h
  simp only [Pi.smul_apply,smul_eq_mul,gaussianPDF,←ENNReal.ofReal_mul (sq_nonneg β),
    ←ENNReal.ofReal_mul (sq_nonneg z)]
  exact ENNReal.ofReal_le_ofReal (scaled_field_pdf_mono hβ hβz hz h)

lemma scaled_integral_mono {β z : ℝ} (hβ : 0 < β) (hβz : β ≤ z) (hz : z ≤ 1)
    {f : ℝ → ℝ} (hf : ∀ h, 0 ≤ f h) (hfi : Integrable f (fieldLaw z)) :
    β^2*(∫ h, f h ∂fieldLaw β) ≤ z^2*(∫ h, f h ∂fieldLaw z) := by
  have h := integral_mono_measure (scaled_fieldLaw_mono hβ hβz hz)
    (ae_of_all _ hf) (hfi.smul_measure ENNReal.ofReal_ne_top)
  simpa only [integral_smul_measure,ENNReal.toReal_ofReal (sq_nonneg _),smul_eq_mul] using h

lemma integral_diagonal_kernel {μ : Measure ℝ} [IsProbabilityMeasure μ] (h : ℝ) :
    Integrable (fun t => v t^2/(w h+w t)) μ := by
  apply (integrable_const (2:ℝ)).mono'
    (continuous_diagonal_kernel.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  exact ae_of_all _ (fun t => by
    simpa only [norm_eq_abs,Function.comp_apply,id_eq] using abs_diagonal_kernel_le h t)

lemma diagonal_temperature_mono {β z : ℝ} (hβ : 0 < β) (hβz : β ≤ z) (hz : z ≤ 1) (h : ℝ) :
    diagonal (fieldLaw β) β h ≤ diagonal (fieldLaw z) z h := by
  apply scaled_integral_mono hβ hβz hz
    (fun t => div_nonneg (sq_nonneg _) (add_pos (w_pos h) (w_pos t)).le)
    (integral_diagonal_kernel h)

lemma cost_temperature_mono {β z : ℝ} (hβ : 0 < β) (hβz : β ≤ z) (hz : z ≤ 1) (t : ℝ) :
    cost (fieldLaw β) β t ≤ cost (fieldLaw z) z t := by
  have hi : Integrable (fun h => (v h+v t)^2/(4*multiplier h)) (fieldLaw z) := by
    have hehe (h : ℝ) : (v h+v t)^2/(4*multiplier h) =
        ((1:ℝ)^2/4)*(v h+v t)^2/multiplier h := by ring
    simp_rw [hehe]
    exact (integrable_const (3:ℝ)).mono'
      ((continuous_cost_integrand 1).comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
      (ae_of_all _ (fun h => by simpa only [norm_eq_abs,one_pow,mul_one] using abs_cost_integrand_le 1 h t))
  have he (B h : ℝ) : (B^2/4)*(v h+v t)^2/multiplier h =
      B^2*((v h+v t)^2/(4*multiplier h)) := by ring
  unfold cost
  simp_rw [he,integral_const_mul]
  exact scaled_integral_mono hβ hβz hz
    (fun h => div_nonneg (sq_nonneg _) (mul_pos (by norm_num) (multiplier_strict_pos h)).le) hi

end SKRatio.Scalar

end

end OAI
