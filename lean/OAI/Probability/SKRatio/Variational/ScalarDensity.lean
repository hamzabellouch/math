import Mathlib
import OAI.Probability.SKRatio.Variational.ScalarVariance

namespace OAI

noncomputable section
open scoped Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Real
namespace SKRatio.Scalar

lemma field_pdf_ratio {β z : ℝ} (hβ : 0 < β) (hz : 0 < z) (h : ℝ) :
    gaussianPDFReal (β^2) (variance β) h =
      (z/β)*exp ((z^2-β^2)/2+(1/(2*z^2)-1/(2*β^2))*h^2)*
      gaussianPDFReal (z^2) (variance z) h := by
  rw [field_pdf hβ,field_pdf hz]
  have he : (z^2-β^2)/2+(1/(2*z^2)-1/(2*β^2))*h^2 +
      (-z^2/2+h-h^2/(2*z^2)) = -β^2/2+h-h^2/(2*β^2) := by ring
  calc
    _ = (z/β)*(sqrt (2*Real.pi)*z)⁻¹*exp (-β^2/2+h-h^2/(2*β^2)) := by
      field_simp
    _ = _ := by rw [←he,exp_add]; ring

def densityFactor (β z : ℝ) : ℝ := z/β*exp ((z^2-β^2)/2)

lemma densityFactor_pos {β z : ℝ} (hβ : 0 < β) (hz : 0 < z) :
    0 < densityFactor β z := mul_pos (div_pos hz hβ) (exp_pos _)

lemma field_pdf_le_factor {β z : ℝ} (hβ : 0 < β) (hβz : β ≤ z) (h : ℝ) :
    gaussianPDFReal (β^2) (variance β) h ≤
      densityFactor β z*gaussianPDFReal (z^2) (variance z) h := by
  have hz : 0 < z := hβ.trans_le hβz
  rw [field_pdf_ratio hβ hz]
  have hi : 1/(2*z^2) ≤ 1/(2*β^2) := by
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  apply mul_le_mul_of_nonneg_right _ (gaussianPDFReal_nonneg _ _ _)
  apply mul_le_mul_of_nonneg_left _ (div_pos hz hβ).le
  apply exp_le_exp.mpr
  have hh := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hi) (sq_nonneg h)
  linarith

lemma densityFactor_mono_left {j β z : ℝ} (hj : 0 < j) (hjβ : j ≤ β) (hβz : β ≤ z) :
    densityFactor β z ≤ densityFactor j z := by
  have hβ : 0 < β := hj.trans_le hjβ
  have hz : 0 < z := hβ.trans_le hβz
  apply mul_le_mul
  · exact div_le_div_of_nonneg_left hz.le hj hjβ
  · apply exp_le_exp.mpr
    nlinarith
  · exact (exp_pos _).le
  · exact (div_pos hz hj).le

lemma fieldLaw_le_factor {β z : ℝ} (hβ : 0 < β) (hβz : β ≤ z) :
    fieldLaw β ≤ ENNReal.ofReal (densityFactor β z) • fieldLaw z := by
  have hz : 0 < z := hβ.trans_le hβz
  rw [fieldLaw,fieldLaw,gaussianReal_of_var_ne_zero _ (variance_ne_zero hβ),
    gaussianReal_of_var_ne_zero _ (variance_ne_zero hz),
    ←withDensity_smul' _ _ ENNReal.ofReal_ne_top]
  apply withDensity_mono
  apply ae_of_all
  intro h
  simp only [Pi.smul_apply,smul_eq_mul,gaussianPDF,
    ←ENNReal.ofReal_mul (densityFactor_pos hβ hz).le]
  exact ENNReal.ofReal_le_ofReal (field_pdf_le_factor hβ hβz h)

lemma fieldLaw_le_interval_factor {j β z : ℝ} (hj : 0 < j) (hjβ : j ≤ β) (hβz : β ≤ z) :
    fieldLaw β ≤ ENNReal.ofReal (densityFactor j z) • fieldLaw z := by
  apply (fieldLaw_le_factor (hj.trans_le hjβ) hβz).trans
  intro s
  simp only [Measure.smul_apply,smul_eq_mul]
  exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (densityFactor_mono_left hj hjβ hβz)) (bot_le : (0:ENNReal) ≤ _)

lemma sd_temperature_bound {β z : ℝ} (hβ : 0 < β) (hβz : β ≤ z)
    {f : ℝ → ℝ} (hf : MemLp f 2 (fieldLaw β)) (hf' : MemLp f 2 (fieldLaw z)) :
    sd (fieldLaw β) f ≤ sqrt (densityFactor β z)*sd (fieldLaw z) f :=
  sd_mono_measure_sqrt (densityFactor_pos hβ (hβ.trans_le hβz)).le
    (fieldLaw_le_factor hβ hβz) hf hf'

lemma sd_temperature_interval_bound {j β z : ℝ} (hj : 0 < j) (hjβ : j ≤ β) (hβz : β ≤ z)
    {f : ℝ → ℝ} (hf : MemLp f 2 (fieldLaw β)) (hf' : MemLp f 2 (fieldLaw z)) :
    sd (fieldLaw β) f ≤ sqrt (densityFactor j z)*sd (fieldLaw z) f :=
  sd_mono_measure_sqrt (densityFactor_pos hj (hj.trans_le (hjβ.trans hβz))).le
    (fieldLaw_le_interval_factor hj hjβ hβz) hf hf'

end SKRatio.Scalar

end

end OAI
