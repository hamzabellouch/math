import Mathlib
import OAI.Probability.SKRatio.Quantization.BinStability
import OAI.Probability.SKRatio.Variational.FieldRadical
import OAI.Probability.SKRatio.Variational.ScalarVariance

namespace OAI

noncomputable section
open scoped NNReal ENNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real
namespace SKRatio.Bins
open Planted Scalar

variable {μ : Measure ℝ} [IsProbabilityMeasure μ]

def fieldDiagonal (μ : Measure ℝ) (H : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ y, v (H y)^2/(w (H x)+w (H y)) ∂μ

def fieldForm (μ : Measure ℝ) (β : ℝ) (H b r : ℝ → ℝ) : ℝ :=
  (∫ x, (β^2*fieldDiagonal μ H x)*(b x^2+r x^2) ∂μ)+
  (∫ x, b x*H x ∂μ)*(∫ x, b x*v (H x) ∂μ)+
  (∫ x, b x ∂μ)*(∫ x, b x*(H x*v (H x)) ∂μ)-
  β^2*(∫ x, b x ∂μ)*(∫ x, b x*v (H x) ∂μ)+
  2*β^2*(∫ x, b x ∂μ)*(∫ x, b x*(m (H x)*v (H x)) ∂μ)+
  β^2*(∫ z : ℝ×ℝ, b z.1*kernel (H z.1) (H z.2)*b z.2 ∂μ.prod μ)+
  β*(∫ x, r x*sqrt (fieldRadicand μ H b r x) ∂μ)

lemma fieldForm_id (β : ℝ) (b r : ℝ → ℝ) :
    fieldForm (fieldLaw β) β id b r=variational β b r := rfl

lemma measurable_fieldDiagonal {H : ℝ → ℝ} (hH : Measurable H) :
    Measurable (fieldDiagonal μ H) := by
  have hm : StronglyMeasurable (fun z : ℝ×ℝ => v (H z.2)^2/(w (H z.1)+w (H z.2))) :=
    (continuous_diagonal_kernel.measurable.comp
      ((hH.comp measurable_fst).prodMk (hH.comp measurable_snd))).stronglyMeasurable
  exact hm.integral_prod_right.measurable

lemma fieldDiagonal_integrable {H : ℝ → ℝ} (hH : Measurable H) (x : ℝ) :
    Integrable (fun y => v (H y)^2/(w (H x)+w (H y))) μ := by
  apply (integrable_const (2:ℝ)).mono'
    (continuous_diagonal_kernel.measurable.comp (measurable_const.prodMk hH)).aestronglyMeasurable
  exact ae_of_all _ (fun y => by simpa only [norm_eq_abs,Function.comp_apply] using abs_diagonal_kernel_le (H x) (H y))

lemma abs_fieldDiagonal_le {H : ℝ → ℝ} (hH : Measurable H) (x : ℝ) :
    |fieldDiagonal μ H x| ≤ 2 :=
  integral_abs_bound (fieldDiagonal_integrable hH x)
    (fun point => abs_diagonal_kernel_le (H x) (H point))

lemma fieldDiagonal_error {H H' : ℝ → ℝ} (hH : Measurable H) (hH' : Measurable H')
    {a : ℝ} (hf : ∀ x y, |v (H y)^2/(w (H x)+w (H y))-
      v (H' y)^2/(w (H' x)+w (H' y))| ≤ a) (x : ℝ) :
    |fieldDiagonal μ H x-fieldDiagonal μ H' x| ≤ a := by
  unfold fieldDiagonal
  rw [←integral_sub (fieldDiagonal_integrable hH x) (fieldDiagonal_integrable hH' x)]
  exact integral_abs_bound ((fieldDiagonal_integrable hH x).sub (fieldDiagonal_integrable hH' x)) (hf x)

lemma fieldKernel_integrable {H b : ℝ → ℝ} (hH : Measurable H) (hb : MemLp b 2 μ) :
    Integrable (fun z : ℝ×ℝ => b z.1*kernel (H z.1) (H z.2)*b z.2) (μ.prod μ) := by
  have hI := hb.integrable (by norm_num : (1:ENNReal) ≤ 2)
  apply (hI.norm.mul_prod hI.norm).mono'
    ((hb.aestronglyMeasurable.comp_fst.mul
      (continuous_kernel.measurable.comp ((hH.comp measurable_fst).prodMk
        (hH.comp measurable_snd))).aestronglyMeasurable).mul hb.aestronglyMeasurable.comp_snd)
  exact ae_of_all _ (fun z => by
    change |b z.1*kernel (H z.1) (H z.2)*b z.2| ≤ |b z.1| * |b z.2|
    simp only [abs_mul]
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (abs_kernel_le_one (H z.1) (H z.2)) (abs_nonneg (b z.1))) (abs_nonneg (b z.2))
    simpa only [mul_one] using hh)

lemma fieldKernel_error {H H' b : ℝ → ℝ} (hH : Measurable H) (hH' : Measurable H')
    (hb : MemLp b 2 μ) (hb1 : l2Norm μ b ≤ 1) {a : ℝ} (ha : 0 ≤ a)
    (hk : ∀ x y, |kernel (H x) (H y)-kernel (H' x) (H' y)| ≤ a) :
    |(∫ z : ℝ×ℝ, b z.1*kernel (H z.1) (H z.2)*b z.2 ∂μ.prod μ)-
      (∫ z : ℝ×ℝ, b z.1*kernel (H' z.1) (H' z.2)*b z.2 ∂μ.prod μ)| ≤ a := by
  have hI := hb.integrable (by norm_num : (1:ENNReal) ≤ 2)
  rw [←integral_sub (fieldKernel_integrable hH hb) (fieldKernel_integrable hH' hb)]
  apply abs_integral_le_integral_abs.trans
  have hi := integral_mono ((fieldKernel_integrable hH hb).sub (fieldKernel_integrable hH' hb)).abs
    ((hI.abs.mul_prod hI.abs).const_mul a) (fun z : ℝ×ℝ => by
      change |b z.1*kernel (H z.1) (H z.2)*b z.2-b z.1*kernel (H' z.1) (H' z.2)*b z.2| ≤ a*(|b z.1| * |b z.2|)
      rw [show b z.1*kernel (H z.1) (H z.2)*b z.2-b z.1*kernel (H' z.1) (H' z.2)*b z.2=
        (kernel (H z.1) (H z.2)-kernel (H' z.1) (H' z.2))*(b z.1*b z.2) by ring,abs_mul,abs_mul]
      exact mul_le_mul_of_nonneg_right (hk z.1 z.2) (mul_nonneg (abs_nonneg _) (abs_nonneg _)))
  rw [integral_const_mul,integral_prod_mul (fun x => |b x|) (fun x => |b x|)] at hi
  apply hi.trans
  have hn : 0 ≤ ∫ x, |b x| ∂μ := integral_nonneg (fun x => abs_nonneg (b x))
  have hh := (integral_abs_le_l2 hb).trans hb1
  nlinarith only [mul_nonneg ha (sub_nonneg.mpr hh),
    mul_nonneg (mul_nonneg ha hn) (sub_nonneg.mpr hh)]

omit [IsProbabilityMeasure μ] in
lemma field_pair_difference {b f g : ℝ → ℝ} (hb : MemLp b 2 μ)
    (hb1 : l2Norm μ b ≤ 1) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    |(∫ x, b x*f x ∂μ)-(∫ x, b x*g x ∂μ)| ≤ l2Norm μ (fun x => f x-g x) := by
  have hfi : Integrable (fun x => b x*f x) μ := hb.integrable_mul hf
  have hgi : Integrable (fun x => b x*g x) μ := hb.integrable_mul hg
  rw [←integral_sub hfi hgi]
  simp_rw [←mul_sub]
  exact field_pair_abs_le hb (hf.sub hg) hb1

lemma field_pair_v_abs {b H : ℝ → ℝ} (hb : MemLp b 2 μ) (hb1 : l2Norm μ b ≤ 1)
    (hH : Measurable H) : |∫ x, b x*v (H x) ∂μ| ≤ 1 :=
  (field_pair_abs_le hb (memLp_bounded (continuous_v.measurable.comp hH)
    (fun x => v_abs_le_one (H x))) hb1).trans
    (l2Norm_le_bounded (continuous_v.measurable.comp hH) (by norm_num) (fun x => v_abs_le_one (H x)))

lemma mean_abs_le_one {b : ℝ → ℝ} (hb : MemLp b 2 μ) (hb1 : l2Norm μ b ≤ 1) :
    |∫ x, b x ∂μ| ≤ 1 := (abs_integral_le_integral_abs.trans (integral_abs_le_l2 hb)).trans hb1

omit [IsProbabilityMeasure μ] in
lemma memLp_Hv {H : ℝ → ℝ} (hH : Measurable H) (hH2 : MemLp H 2 μ) :
    MemLp (fun x => H x*v (H x)) 2 μ :=
  memLp_field_mul hH2 (continuous_v.measurable.comp hH) (fun point => v_abs_le_one (H point))

omit [IsProbabilityMeasure μ] in
lemma Hv_error {H H' : ℝ → ℝ} (hH : Measurable H) (hH' : Measurable H')
    (hH2 : MemLp H 2 μ) (hH2' : MemLp H' 2 μ)
    {a d T : ℝ} (ha : 0 ≤ a) (he : l2Norm μ (fun x => H x-H' x) ≤ d)
    (hsize : l2Norm μ H' ≤ T) (hv : ∀ x, |v (H x)-v (H' x)| ≤ a) :
    l2Norm μ (fun x => H x*v (H x)-H' x*v (H' x)) ≤ d+T*a := by
  have heq : (fun x => H x*v (H x)-H' x*v (H' x))=
      (fun x => (H x-H' x)*v (H x)+H' x*(v (H x)-v (H' x))) := by funext x; ring
  rw [heq]
  have h1 := l2Norm_field_mul (hH2.sub hH2') (continuous_v.measurable.comp hH)
    (by norm_num : (0:ℝ) ≤ 1) (fun x => v_abs_le_one _)
  have h2 := l2Norm_field_mul hH2'
    ((continuous_v.measurable.comp hH).sub (continuous_v.measurable.comp hH')) ha hv
  have ht := l2Norm_add (memLp_field_mul (hH2.sub hH2')
    (continuous_v.measurable.comp hH) (fun x => v_abs_le_one _))
    (memLp_field_mul hH2' ((continuous_v.measurable.comp hH).sub (continuous_v.measurable.comp hH')) hv)
  have h3 := mul_le_mul_of_nonneg_left hsize ha
  simp only [Pi.sub_apply,Pi.sub_def,Function.comp_apply] at h1 h2 ht
  nlinarith only [h1,h2,ht,h3,he]

lemma field_radical_pair_error {b r H H' : ℝ → ℝ} (hb : MemLp b 2 μ) (hr : MemLp r 2 μ)
    (hbm : Measurable b) (hrm : Measurable r) (hH : Measurable H) (hH' : Measurable H')
    (he : (∫ x, b x^2+r x^2 ∂μ)=1) {a : ℝ} (ha : 0 ≤ a)
    (hv : ∀ x, |v (H x)-v (H' x)| ≤ a) :
    |(∫ x, r x*sqrt (fieldRadicand μ H b r x) ∂μ)-
      (∫ x, r x*sqrt (fieldRadicand μ H' b r x) ∂μ)| ≤ 4*sqrt a := by
  apply bounded_pair_error hr (norm_components hb hr he).2
    ((measurable_fieldRadicand hbm hrm hH).sqrt) ((measurable_fieldRadicand hbm hrm hH').sqrt)
    (C := 2) (D := 2) _ _ (by positivity) (sqrt_fieldRadicand_error hb hr hH hH' he ha hv)
  · intro x
    rw [abs_of_nonneg (sqrt_nonneg _)]
    exact (sqrt_le_iff).mpr ⟨by norm_num,by norm_num only [show (2:ℝ)^2=4 by norm_num]; exact fieldRadicand_le hb hr hH he x⟩
  · intro x
    rw [abs_of_nonneg (sqrt_nonneg _)]
    exact (sqrt_le_iff).mpr ⟨by norm_num,by norm_num only [show (2:ℝ)^2=4 by norm_num]; exact fieldRadicand_le hb hr hH' he x⟩

theorem fieldForm_error {b r H H' : ℝ → ℝ} (β : ℝ) (hβ : 0 ≤ β)
    (hb : MemLp b 2 μ) (hr : MemLp r 2 μ) (hbm : Measurable b) (hrm : Measurable r)
    (hH : Measurable H) (hH' : Measurable H') (hH2 : MemLp H 2 μ) (hH2' : MemLp H' 2 μ)
    (he : (∫ x, b x^2+r x^2 ∂μ)=1) {a d T : ℝ} (ha : 0 ≤ a) (hT : 0 ≤ T)
    (herr : l2Norm μ (fun x => H x-H' x) ≤ d) (hsize : l2Norm μ H' ≤ T)
    (hv : ∀ x, |v (H x)-v (H' x)| ≤ a)
    (hmv : ∀ x, |m (H x)*v (H x)-m (H' x)*v (H' x)| ≤ a)
    (hf : ∀ x y, |v (H y)^2/(w (H x)+w (H y))-
      v (H' y)^2/(w (H' x)+w (H' y))| ≤ a)
    (hk : ∀ x y, |kernel (H x) (H y)-kernel (H' x) (H' y)| ≤ a) :
    |fieldForm μ β H b r-fieldForm μ β H' b r| ≤
      2*d+2*T*a+5*β^2*a+4*β*sqrt a := by
  have hb1 := (norm_components hb hr he).1
  have hV := bounded_pair_error hb hb1 (continuous_v.measurable.comp hH)
    (continuous_v.measurable.comp hH') (fun x => v_abs_le_one _) (fun x => v_abs_le_one _) ha hv
  have hmabs (x : ℝ) : |m x*v x| ≤ 1 := by
    have hm : |m x| ≤ 1 := abs_le.mpr ⟨(m_bounds x).1.le,(m_bounds x).2.le⟩
    rw [abs_mul]
    simpa only [mul_one] using mul_le_mul hm (v_abs_le_one x) (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
  have hMV := bounded_pair_error hb hb1
    ((continuous_m.mul continuous_v).measurable.comp hH)
    ((continuous_m.mul continuous_v).measurable.comp hH')
    (fun x => hmabs _) (fun x => hmabs _) ha hmv
  have hHv := (field_pair_difference hb hb1 (memLp_Hv hH hH2)
    (memLp_Hv hH' hH2')).trans (Hv_error hH hH' hH2 hH2' ha herr hsize hv)
  have h₁ := product_error (by norm_num : (0:ℝ) ≤ 1) hT (field_pair_v_abs hb hb1 hH)
    ((field_pair_abs_le hb hH2' hb1).trans hsize)
    ((field_pair_difference hb hb1 hH2 hH2').trans herr) hV
  have h₂ : |(∫ x, b x ∂μ)*(∫ x, b x*(H x*v (H x)) ∂μ)-
      (∫ x, b x ∂μ)*(∫ x, b x*(H' x*v (H' x)) ∂μ)| ≤ d+T*a := by
    rw [←mul_sub,abs_mul]
    exact (mul_le_mul (mean_abs_le_one hb hb1) hHv (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)).trans_eq (one_mul _)
  have h₃ : |β^2*(∫ x, b x ∂μ)*((∫ x, b x*v (H x) ∂μ)-
      (∫ x, b x*v (H' x) ∂μ))| ≤ β^2*a := by
    rw [abs_mul,abs_mul,abs_of_nonneg (sq_nonneg β)]
    exact mul_le_mul ((mul_le_mul_of_nonneg_left (mean_abs_le_one hb hb1) (sq_nonneg β)).trans_eq (mul_one _))
      hV (abs_nonneg _) (sq_nonneg β)
  have h₄ : |2*β^2*(∫ x, b x ∂μ)*((∫ x, b x*(m (H x)*v (H x)) ∂μ)-
      (∫ x, b x*(m (H' x)*v (H' x)) ∂μ))| ≤ 2*β^2*a := by
    rw [abs_mul,abs_mul,abs_of_nonneg (by positivity : 0 ≤ 2*β^2)]
    exact mul_le_mul ((mul_le_mul_of_nonneg_left (mean_abs_le_one hb hb1) (by positivity : 0 ≤ 2*β^2)).trans_eq (mul_one _))
      hMV (abs_nonneg _) (by positivity)
  have hd := energy_error hb hr he (measurable_fieldDiagonal (μ := μ) hH) (measurable_fieldDiagonal (μ := μ) hH')
    (abs_fieldDiagonal_le hH) (abs_fieldDiagonal_le hH') (fieldDiagonal_error hH hH' hf)
  have h₅ : |(∫ x, (β^2*fieldDiagonal μ H x)*(b x^2+r x^2) ∂μ)-
      (∫ x, (β^2*fieldDiagonal μ H' x)*(b x^2+r x^2) ∂μ)| ≤ β^2*a := by
    simp_rw [mul_assoc,integral_const_mul]
    rw [←mul_sub,abs_mul,abs_of_nonneg (sq_nonneg β)]
    exact mul_le_mul_of_nonneg_left hd (sq_nonneg β)
  have h₆ : |β^2*((∫ z : ℝ×ℝ, b z.1*kernel (H z.1) (H z.2)*b z.2 ∂μ.prod μ)-
      (∫ z : ℝ×ℝ, b z.1*kernel (H' z.1) (H' z.2)*b z.2 ∂μ.prod μ))| ≤ β^2*a := by
    rw [abs_mul,abs_of_nonneg (sq_nonneg β)]
    exact mul_le_mul_of_nonneg_left (fieldKernel_error hH hH' hb hb1 ha hk) (sq_nonneg β)
  have h₇ : |β*((∫ x, r x*sqrt (fieldRadicand μ H b r x) ∂μ)-
      (∫ x, r x*sqrt (fieldRadicand μ H' b r x) ∂μ))| ≤ 4*β*sqrt a := by
    rw [abs_mul,abs_of_nonneg hβ]
    have hh := mul_le_mul_of_nonneg_left (field_radical_pair_error hb hr hbm hrm hH hH' he ha hv) hβ
    nlinarith only [hh]
  unfold fieldForm
  simp only [Function.comp_apply] at h₁
  have bounds₁ := abs_le.mp h₁
  have bounds₂ := abs_le.mp h₂
  have bounds₃ := abs_le.mp h₃
  have bounds₄ := abs_le.mp h₄
  have bounds₅ := abs_le.mp h₅
  have bounds₆ := abs_le.mp h₆
  have bounds₇ := abs_le.mp h₇
  exact abs_le.mpr ⟨by nlinarith only [bounds₁.1,bounds₂.1,bounds₃.2,bounds₄.1,bounds₅.1,bounds₆.1,bounds₇.1],
    by nlinarith only [bounds₁.2,bounds₂.2,bounds₃.1,bounds₄.2,bounds₅.2,bounds₆.2,bounds₇.2]⟩

end SKRatio.Bins

end

end OAI
