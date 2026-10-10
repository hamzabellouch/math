import Mathlib
import OAI.Probability.SKRatio.Variational.ScalarCoherent
import OAI.Probability.SKRatio.Variational.ScalarTemperature

namespace OAI

noncomputable section
open scoped Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Real
namespace SKRatio.Scalar

section Norm
variable {μ : Measure ℝ}

lemma l2Norm_add {f g : ℝ → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    l2Norm μ (fun x => f x+g x) ≤ l2Norm μ f+l2Norm μ g := by
  have he := integral_square_add hf hg 1 1
  simp only [one_mul,one_pow,mul_one] at he
  have hcs := (le_abs_self _).trans (abs_integral_mul_le hf hg)
  apply (sq_le_sq₀ (l2Norm_nonneg _) (add_nonneg (l2Norm_nonneg _) (l2Norm_nonneg _))).mp
  rw [l2Norm_sq,he]
  nlinarith only [hcs,l2Norm_sq (μ := μ) f,l2Norm_sq (μ := μ) g]

lemma l2Norm_const_mul (f : ℝ → ℝ) (c : ℝ) :
    l2Norm μ (fun x => c*f x) = |c| *l2Norm μ f := by
  apply (sq_eq_sq₀ (l2Norm_nonneg _) (mul_nonneg (abs_nonneg _) (l2Norm_nonneg _))).mp
  simp only [l2Norm_sq,mul_pow,integral_const_mul,sq_abs]

end Norm
section Probability
variable {μ ν : Measure ℝ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

omit [IsProbabilityMeasure μ] in
lemma sd_sq (f : ℝ → ℝ) : sd μ f^2 = ∫ x, centered μ f x^2 ∂μ := l2Norm_sq _

lemma sd_sq_eq {f : ℝ → ℝ} (hf : MemLp f 2 μ) :
    sd μ f^2 = (∫ x, f x^2 ∂μ)-(∫ x, f x ∂μ)^2 := by
  rw [sd_sq]
  exact integral_centered_sq hf

lemma square_center_expansion {f : ℝ → ℝ} (hf : MemLp f 2 μ) (c : ℝ) :
    ∫ x, (f x-c)^2 ∂μ = sd μ f^2+((∫ x, f x ∂μ)-c)^2 := by
  have he := integral_square_add hf (memLp_const (1:ℝ)) 1 (-c)
  simp only [one_mul,one_pow,mul_one,one_mul,←sub_eq_add_neg,neg_sq,
    integral_const,probReal_univ,smul_eq_mul,one_mul] at he
  rw [he,sd_sq_eq hf]
  ring

lemma sd_min_center {f : ℝ → ℝ} (hf : MemLp f 2 μ) (c : ℝ) :
    sd μ f^2 ≤ ∫ x, (f x-c)^2 ∂μ := by
  rw [square_center_expansion hf c]
  exact le_add_of_nonneg_right (sq_nonneg _)

omit [IsProbabilityMeasure μ] in
lemma centered_add {f g : ℝ → ℝ} (hf : Integrable f μ) (hg : Integrable g μ) :
    centered μ (fun x => f x+g x) = fun x => centered μ f x+centered μ g x := by
  ext x
  simp only [centered,integral_add hf hg]
  ring

omit [IsProbabilityMeasure μ] in
lemma centered_const_mul (f : ℝ → ℝ) (c : ℝ) :
    centered μ (fun x => c*f x) = fun x => c*centered μ f x := by
  ext x
  simp only [centered,integral_const_mul]
  ring

lemma centered_sub_const {f : ℝ → ℝ} (hf : Integrable f μ) (c : ℝ) :
    centered μ (fun x => f x-c) = centered μ f := by
  ext x
  simp only [centered,integral_sub hf (integrable_const _),integral_const,
    probReal_univ,smul_eq_mul,one_mul]
  ring

lemma sd_add {f g : ℝ → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    sd μ (fun x => f x+g x) ≤ sd μ f+sd μ g := by
  unfold sd
  rw [centered_add (hf.integrable (by norm_num)) (hg.integrable (by norm_num))]
  exact l2Norm_add (memLp_centered hf) (memLp_centered hg)

omit [IsProbabilityMeasure μ] in
lemma sd_const_mul (f : ℝ → ℝ) (c : ℝ) :
    sd μ (fun x => c*f x) = |c| *sd μ f := by
  unfold sd
  rw [centered_const_mul,l2Norm_const_mul]

lemma sd_sub_const {f : ℝ → ℝ} (hf : MemLp f 2 μ) (c : ℝ) :
    sd μ (fun x => f x-c) = sd μ f := by
  unfold sd
  rw [centered_sub_const (hf.integrable (by norm_num))]

lemma sd_sub {f g : ℝ → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    sd μ (fun x => f x-g x) ≤ sd μ f+sd μ g := by
  have he (x : ℝ) : f x-g x = f x+(-1)*g x := by ring
  simp_rw [he]
  have hh := sd_add hf (hg.const_mul (-1))
  simpa only [sd_const_mul,abs_neg,abs_one,one_mul] using hh

lemma abs_sd_sub_le {f g : ℝ → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    |sd μ f-sd μ g| ≤ sd μ (fun x => f x-g x) := by
  have h1 := sd_add (hf.sub hg) hg
  have h2 := sd_sub hf (hf.sub hg)
  simp only [Pi.sub_apply,sub_add_cancel,sub_sub_cancel] at h1 h2
  change sd μ f ≤ sd μ (fun x => f x-g x)+sd μ g at h1
  change sd μ g ≤ sd μ f+sd μ (fun x => f x-g x) at h2
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma sd_mono_measure {C : ℝ} (hC : 0 ≤ C)
    (hμν : μ ≤ ENNReal.ofReal C • ν)
    {f : ℝ → ℝ} (hf : MemLp f 2 μ) (hf' : MemLp f 2 ν) :
    sd μ f^2 ≤ C*sd ν f^2 := by
  calc
    sd μ f^2 ≤ ∫ x, (f x-(∫ y, f y ∂ν))^2 ∂μ := sd_min_center hf _
    _ ≤ ∫ x, (f x-(∫ y, f y ∂ν))^2 ∂(ENNReal.ofReal C • ν) :=
      integral_mono_measure hμν (ae_of_all _ (fun _ => sq_nonneg _))
        ((memLp_centered hf').integrable_sq.smul_measure ENNReal.ofReal_ne_top)
    _ = C*sd ν f^2 := by
      rw [integral_smul_measure,ENNReal.toReal_ofReal hC,smul_eq_mul,sd_sq]
      rfl

lemma sd_mono_measure_sqrt {C : ℝ} (hC : 0 ≤ C)
    (hμν : μ ≤ ENNReal.ofReal C • ν)
    {f : ℝ → ℝ} (hf : MemLp f 2 μ) (hf' : MemLp f 2 ν) :
    sd μ f ≤ sqrt C*sd ν f := by
  apply (sq_le_sq₀ (sd_nonneg _) (mul_nonneg (sqrt_nonneg _) (sd_nonneg _))).mp
  rw [mul_pow,sq_sqrt hC]
  exact sd_mono_measure hC hμν hf hf'

lemma weighted_sd_mono_measure {B Z : ℝ} (hB : 0 ≤ B) (hZ : 0 ≤ Z)
    (hμν : ENNReal.ofReal B • μ ≤ ENNReal.ofReal Z • ν)
    {f : ℝ → ℝ} (hf : MemLp f 2 μ) (hf' : MemLp f 2 ν) :
    B*sd μ f^2 ≤ Z*sd ν f^2 := by
  calc
    B*sd μ f^2 ≤ B*(∫ x, (f x-(∫ y, f y ∂ν))^2 ∂μ) :=
      mul_le_mul_of_nonneg_left (sd_min_center hf _) hB
    _ = ∫ x, (f x-(∫ y, f y ∂ν))^2 ∂(ENNReal.ofReal B • μ) := by
      rw [integral_smul_measure,ENNReal.toReal_ofReal hB,smul_eq_mul]
    _ ≤ ∫ x, (f x-(∫ y, f y ∂ν))^2 ∂(ENNReal.ofReal Z • ν) :=
      integral_mono_measure hμν (ae_of_all _ (fun _ => sq_nonneg _))
        ((memLp_centered hf').integrable_sq.smul_measure ENNReal.ofReal_ne_top)
    _ = Z*sd ν f^2 := by
      rw [integral_smul_measure,ENNReal.toReal_ofReal hZ,smul_eq_mul,sd_sq]
      rfl
end Probability

lemma weighted_sd_temperature_mono {β z : ℝ} (hβ : 0 < β) (hβz : β ≤ z) (hz : z ≤ 1)
    {f : ℝ → ℝ} (hf : MemLp f 2 (fieldLaw β)) (hf' : MemLp f 2 (fieldLaw z)) :
    β^2*sd (fieldLaw β) f^2 ≤ z^2*sd (fieldLaw z) f^2 :=
  weighted_sd_mono_measure (sq_nonneg _) (sq_nonneg _)
    (scaled_fieldLaw_mono hβ hβz hz) hf hf'

lemma weighted_sd_temperature_mono' {β z : ℝ} (hβ : 0 < β) (hβz : β ≤ z) (hz : z ≤ 1)
    {f : ℝ → ℝ} (hf : MemLp f 2 (fieldLaw β)) (hf' : MemLp f 2 (fieldLaw z)) :
    β*sd (fieldLaw β) f ≤ z*sd (fieldLaw z) f := by
  apply (sq_le_sq₀ (mul_nonneg hβ.le (sd_nonneg _))
    (mul_nonneg (hβ.le.trans hβz) (sd_nonneg _))).mp
  simpa only [mul_pow] using weighted_sd_temperature_mono hβ hβz hz hf hf'

lemma weighted_mv_temperature_mono {β z : ℝ} (hβ : 0 < β) (hβz : β ≤ z) (hz : z ≤ 1) :
    β^2*(∫ h, m h*v h ∂fieldLaw β) ≤ z^2*(∫ h, m h*v h ∂fieldLaw z) := by
  simp_rw [mean_mv_eq_mean_m_sq_v]
  apply scaled_integral_mono hβ hβz hz (fun h => mul_nonneg (sq_nonneg _) (v_pos h).le)
  apply (integrable_const (1:ℝ)).mono'
    ((continuous_m.pow 2).mul continuous_v).aestronglyMeasurable
  apply ae_of_all
  intro h
  change |m h^2*v h| ≤ 1
  rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) (v_pos h).le)]
  exact (mul_le_mul_of_nonneg_right (tanh_sq_lt_one h).le (v_pos h).le).trans (by simpa using v_le_one h)

lemma weighted_R_temperature_mono {β z : ℝ} (hβ : 0 < β) (hβz : β ≤ z) (hz : z ≤ 1) :
    β^2*R β ≤ z^2*R z := by
  apply scaled_integral_mono hβ hβz hz rho_nonneg
  exact integrable_rho

end SKRatio.Scalar

end

end OAI
