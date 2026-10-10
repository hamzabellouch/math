import Mathlib
import OAI.Probability.SKRatio.Variational.ScalarHilbert

namespace OAI

noncomputable section
open scoped NNReal ENNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real
namespace SKRatio.Bins
open Planted Scalar

variable {μ : Measure ℝ} [IsProbabilityMeasure μ]

lemma memLp_bounded {f : ℝ → ℝ} (hf : Measurable f) {C : ℝ}
    (hC : ∀ x, |f x| ≤ C) : MemLp f 2 μ :=
  MemLp.of_bound hf.aestronglyMeasurable C (ae_of_all _ (fun x => by
    simpa only [norm_eq_abs] using hC x))

lemma l2Norm_le_bounded {f : ℝ → ℝ} (hf : Measurable f) {C : ℝ}
    (hC : 0 ≤ C) (hfC : ∀ x, |f x| ≤ C) : l2Norm μ f ≤ C := by
  have hi := integral_mono (memLp_bounded hf hfC (μ := μ)).integrable_sq
    (integrable_const (C^2)) (fun x => show f x^2 ≤ C^2 by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hC).mpr (hfC x))
  simp only [integral_const,probReal_univ,smul_eq_mul,one_mul] at hi
  have hs := l2Norm_sq (μ := μ) f
  nlinarith only [hi,hs,l2Norm_nonneg (μ := μ) f,hC]

omit [IsProbabilityMeasure μ] in
lemma memLp_field_mul {f u : ℝ → ℝ} (hf : MemLp f 2 μ)
    (hu : Measurable u) {C : ℝ} (hC : ∀ x, |u x| ≤ C) :
    MemLp (fun x => f x*u x) 2 μ := by
  apply hf.of_le_mul (hf.aestronglyMeasurable.mul hu.aestronglyMeasurable) (c := C)
  exact ae_of_all _ (fun x => by
    change |f x*u x| ≤ C*|f x|
    rw [abs_mul]
    nlinarith only [mul_le_mul_of_nonneg_left (hC x) (abs_nonneg (f x))])

omit [IsProbabilityMeasure μ] in
lemma l2Norm_field_mul {f u : ℝ → ℝ} (hf : MemLp f 2 μ)
    (hu : Measurable u) {C : ℝ} (hC : 0 ≤ C) (huC : ∀ x, |u x| ≤ C) :
    l2Norm μ (fun x => f x*u x) ≤ C*l2Norm μ f := by
  have hi := integral_mono (memLp_field_mul hf hu huC).integrable_sq
    (hf.integrable_sq.const_mul (C^2)) (fun x => show (f x*u x)^2 ≤ C^2*f x^2 by
      have hh : u x^2 ≤ C^2 := by
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hC).mpr (huC x)
      simpa only [mul_pow,mul_comm] using mul_le_mul_of_nonneg_left hh (sq_nonneg (f x)))
  rw [integral_const_mul,←l2Norm_sq,←l2Norm_sq] at hi
  have hn := l2Norm_nonneg (μ := μ) (fun x => f x*u x)
  have hn' : 0 ≤ C*l2Norm μ f := mul_nonneg hC (l2Norm_nonneg f)
  nlinarith only [hi,hn,hn']

omit [IsProbabilityMeasure μ] in
lemma norm_components {b r : ℝ → ℝ} (hb : MemLp b 2 μ) (hr : MemLp r 2 μ)
    (he : (∫ x, b x^2+r x^2 ∂μ)=1) : l2Norm μ b ≤ 1 ∧ l2Norm μ r ≤ 1 := by
  rw [integral_add hb.integrable_sq hr.integrable_sq,←l2Norm_sq,←l2Norm_sq] at he
  constructor <;> nlinarith only [he,sq_nonneg (l2Norm μ b),sq_nonneg (l2Norm μ r)]

lemma integral_abs_le_l2 {f : ℝ → ℝ} (hf : MemLp f 2 μ) :
    (∫ x, |f x| ∂μ) ≤ l2Norm μ f := by
  have hh : |∫ x, |f x| * (1:ℝ) ∂μ| ≤ l2Norm μ (fun x => |f x|)*l2Norm μ (fun _ => (1:ℝ)) :=
    abs_integral_mul_le hf.abs (memLp_const (1:ℝ) (μ := μ) (p := 2))
  have he : l2Norm μ (fun x => |f x|)=l2Norm μ f := by simp only [l2Norm,sq_abs]
  have ho : l2Norm μ (fun _ : ℝ => (1:ℝ))=1 := by
    simp only [l2Norm,one_pow,integral_const,probReal_univ,smul_eq_mul,one_mul,sqrt_one]
  simp only [mul_one,he,ho] at hh
  rw [abs_of_nonneg (integral_nonneg (fun x : ℝ => abs_nonneg (f x)))] at hh
  exact hh

omit [IsProbabilityMeasure μ] in
lemma field_pair_abs_le {b f : ℝ → ℝ} (hb : MemLp b 2 μ) (hf : MemLp f 2 μ)
    (hb1 : l2Norm μ b ≤ 1) : |∫ x, b x*f x ∂μ| ≤ l2Norm μ f :=
  (abs_integral_mul_le hb hf).trans (by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hb1 (l2Norm_nonneg f))

lemma integral_abs_bound {f : ℝ → ℝ} (hf : Integrable f μ) {C : ℝ}
    (hC : ∀ x, |f x| ≤ C) : |∫ x, f x ∂μ| ≤ C := by
  apply abs_integral_le_integral_abs.trans
  simpa only [integral_const,probReal_univ,smul_eq_mul,one_mul] using
    integral_mono hf.abs (integrable_const C) hC

lemma bounded_pair_error {b f g : ℝ → ℝ} (hb : MemLp b 2 μ)
    (hb1 : l2Norm μ b ≤ 1) (hf : Measurable f) (hg : Measurable g)
    {C D a : ℝ} (hfC : ∀ x, |f x| ≤ C) (hgD : ∀ x, |g x| ≤ D)
    (ha : 0 ≤ a) (he : ∀ x, |f x-g x| ≤ a) :
    |(∫ x, b x*f x ∂μ)-(∫ x, b x*g x ∂μ)| ≤ a := by
  have hfi : Integrable (fun x => b x*f x) μ := hb.integrable_mul (memLp_bounded hf hfC)
  have hgi : Integrable (fun x => b x*g x) μ := hb.integrable_mul (memLp_bounded hg hgD)
  rw [←integral_sub hfi hgi]
  simp_rw [←mul_sub]
  exact (field_pair_abs_le hb ((memLp_bounded hf hfC).sub (memLp_bounded hg hgD)) hb1).trans
    (l2Norm_le_bounded (hf.sub hg) ha he)

omit [IsProbabilityMeasure μ] in
lemma energy_error {b r f g : ℝ → ℝ} (hb : MemLp b 2 μ) (hr : MemLp r 2 μ)
    (he : (∫ x, b x^2+r x^2 ∂μ)=1)
    (hf : Measurable f) (hg : Measurable g) {C D a : ℝ}
    (hfC : ∀ x, |f x| ≤ C) (hgD : ∀ x, |g x| ≤ D) (hfg : ∀ x, |f x-g x| ≤ a) :
    |(∫ x, f x*(b x^2+r x^2) ∂μ)-(∫ x, g x*(b x^2+r x^2) ∂μ)| ≤ a := by
  have ih : Integrable (fun x => b x^2+r x^2) μ := hb.integrable_sq.add hr.integrable_sq
  have ihf := ih.bdd_mul hf.aestronglyMeasurable (ae_of_all _ (fun x => by simpa only [norm_eq_abs] using hfC x))
  have ihg := ih.bdd_mul hg.aestronglyMeasurable (ae_of_all _ (fun x => by simpa only [norm_eq_abs] using hgD x))
  rw [←integral_sub ihf ihg]
  apply abs_integral_le_integral_abs.trans
  have hi := integral_mono (ihf.sub ihg).abs (ih.const_mul a) (fun x => by
    simp only [Pi.sub_apply,←sub_mul,abs_mul,abs_of_nonneg (add_nonneg (sq_nonneg (b x)) (sq_nonneg (r x)))]
    exact mul_le_mul_of_nonneg_right (hfg x) (add_nonneg (sq_nonneg _) (sq_nonneg _)))
  simpa only [integral_const_mul,Pi.add_apply,Pi.sub_apply,he,mul_one] using hi

lemma sqrt_difference {s t e : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t)
    (he : |s-t| ≤ e) : |sqrt s-sqrt t| ≤ sqrt e := by
  have he0 := (abs_nonneg (s-t)).trans he
  have hs2 := sq_sqrt hs
  have ht2 := sq_sqrt ht
  have he2 := sq_sqrt he0
  have habs : (sqrt s-sqrt t)^2 ≤ e := by
    rcases le_total s t with hst|hts
    · rw [abs_of_nonpos (sub_nonpos.mpr hst)] at he
      have hh := sqrt_le_sqrt hst
      nlinarith only [he,hh,hs2,ht2,mul_nonneg (sqrt_nonneg s) (sub_nonneg.mpr hh)]
    · rw [abs_of_nonneg (sub_nonneg.mpr hts)] at he
      have hh := sqrt_le_sqrt hts
      nlinarith only [he,hh,hs2,ht2,mul_nonneg (sqrt_nonneg t) (sub_nonneg.mpr hh)]
  exact (sq_le_sq₀ (abs_nonneg _) (sqrt_nonneg e)).mp (by simpa only [sq_abs,he2] using habs)

end SKRatio.Bins

end

end OAI
