import Mathlib
import OAI.Probability.SKRatio.Variational.FieldL2

namespace OAI

noncomputable section
open scoped NNReal ENNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real
namespace SKRatio.Bins
open Planted Scalar

variable {μ : Measure ℝ} [IsProbabilityMeasure μ]

def fieldRadicand (μ : Measure ℝ) (H b r : ℝ → ℝ) (x : ℝ) : ℝ :=
  (∫ y, ((v (H x)+v (H y))*r y)^2 ∂μ)+
    (∫ y, ((v (H x)+v (H y))*b y-(∫ t, (v (H x)+v (H t))*b t ∂μ))^2 ∂μ)

omit [IsProbabilityMeasure μ] in
lemma fieldRadicand_nonneg (H b r : ℝ → ℝ) (x : ℝ) :
    0 ≤ fieldRadicand μ H b r x :=
  add_nonneg (integral_nonneg (fun _ => sq_nonneg _))
    (integral_nonneg (fun _ => sq_nonneg _))

omit [IsProbabilityMeasure μ] in
lemma memLp_sum_v_field {b H : ℝ → ℝ} (hb : MemLp b 2 μ) (hH : Measurable H)
    (x : ℝ) : MemLp (fun y => (v (H x)+v (H y))*b y) 2 μ := by
  have hh := memLp_field_mul hb (u := fun y => v (H x)+v (H y))
    (measurable_const.add (continuous_v.measurable.comp hH)) (fun y => abs_v_sum_le (H x) (H y))
  simpa only [mul_comm] using hh

omit [IsProbabilityMeasure μ] in
lemma field_energy_integrable {b r H : ℝ → ℝ} (hb : MemLp b 2 μ) (hr : MemLp r 2 μ)
    (hH : Measurable H) (x : ℝ) :
    Integrable (fun y => (v (H x)+v (H y))^2*(b y^2+r y^2)) μ := by
  have he (y : ℝ) : (v (H x)+v (H y))^2*(b y^2+r y^2)=
      ((v (H x)+v (H y))*b y)^2+((v (H x)+v (H y))*r y)^2 := by ring
  simp_rw [he]
  exact (memLp_sum_v_field hb hH x).integrable_sq.add (memLp_sum_v_field hr hH x).integrable_sq

lemma fieldRadicand_expansion {b r H : ℝ → ℝ} (hb : MemLp b 2 μ) (hr : MemLp r 2 μ)
    (hH : Measurable H) (x : ℝ) : fieldRadicand μ H b r x =
      (∫ y, (v (H x)+v (H y))^2*(b y^2+r y^2) ∂μ)-
        (∫ y, (v (H x)+v (H y))*b y ∂μ)^2 := by
  rw [fieldRadicand,integral_centered_sq (memLp_sum_v_field hb hH x)]
  have he (y : ℝ) : (v (H x)+v (H y))^2*(b y^2+r y^2)=
      ((v (H x)+v (H y))*b y)^2+((v (H x)+v (H y))*r y)^2 := by ring
  simp_rw [he]
  rw [integral_add (memLp_sum_v_field hb hH x).integrable_sq
    (memLp_sum_v_field hr hH x).integrable_sq]
  ring

lemma fieldRadicand_le {b r H : ℝ → ℝ} (hb : MemLp b 2 μ) (hr : MemLp r 2 μ)
    (hH : Measurable H) (he : (∫ x, b x^2+r x^2 ∂μ)=1) (x : ℝ) :
    fieldRadicand μ H b r x ≤ 4 := by
  rw [fieldRadicand_expansion hb hr hH]
  have ih : Integrable (fun y => b y^2+r y^2) μ := hb.integrable_sq.add hr.integrable_sq
  have hi := integral_mono (field_energy_integrable hb hr hH x) (ih.const_mul (4:ℝ))
    (fun y => mul_le_mul_of_nonneg_right (v_sum_sq_le (H x) (H y))
      (add_nonneg (sq_nonneg _) (sq_nonneg _)))
  rw [integral_const_mul,he,mul_one] at hi
  nlinarith only [hi,sq_nonneg (∫ y, (v (H x)+v (H y))*b y ∂μ)]

lemma measurable_fieldRadicand {b r H : ℝ → ℝ} (hb : Measurable b) (hr : Measurable r)
    (hH : Measurable H) : Measurable (fieldRadicand μ H b r) := by
  have hv := continuous_v.measurable.comp hH
  have hm : Measurable (fun x => ∫ t, (v (H x)+v (H t))*b t ∂μ) :=
    (((hv.comp measurable_fst).add (hv.comp measurable_snd)).mul
      (hb.comp measurable_snd)).stronglyMeasurable.integral_prod_right.measurable
  have h1 : Measurable (fun x => ∫ y, ((v (H x)+v (H y))*r y)^2 ∂μ) :=
    ((((hv.comp measurable_fst).add (hv.comp measurable_snd)).mul
      (hr.comp measurable_snd)).pow_const 2).stronglyMeasurable.integral_prod_right.measurable
  have h2 : Measurable (fun x => ∫ y,
      ((v (H x)+v (H y))*b y-(∫ t, (v (H x)+v (H t))*b t ∂μ))^2 ∂μ) :=
    (((((hv.comp measurable_fst).add (hv.comp measurable_snd)).mul
      (hb.comp measurable_snd)).sub (hm.comp measurable_fst)).pow_const 2).stronglyMeasurable.integral_prod_right.measurable
  exact h1.add h2

lemma abs_square_sub_le {x y C e : ℝ} (hC : 0 ≤ C) (hx : |x| ≤ C) (hy : |y| ≤ C)
    (he : |x-y| ≤ e) : |x^2-y^2| ≤ 2*C*e := by
  rw [show x^2-y^2=(x-y)*(x+y) by ring,abs_mul]
  have hsum : |x+y| ≤ 2*C := (abs_add_le _ _).trans (by linarith)
  nlinarith only [mul_le_mul hsum he (abs_nonneg _) (mul_nonneg (by norm_num) hC)]

lemma fieldRadicand_error {b r H H' : ℝ → ℝ} (hb : MemLp b 2 μ) (hr : MemLp r 2 μ)
    (hH : Measurable H) (hH' : Measurable H')
    (he : (∫ x, b x^2+r x^2 ∂μ)=1) {a : ℝ} (ha : 0 ≤ a)
    (hv : ∀ x, |v (H x)-v (H' x)| ≤ a) (x : ℝ) :
    |fieldRadicand μ H b r x-fieldRadicand μ H' b r x| ≤ 16*a := by
  let f := fun y => v (H x)+v (H y)
  let g := fun y => v (H' x)+v (H' y)
  have hf : Measurable f := measurable_const.add (continuous_v.measurable.comp hH)
  have hg : Measurable g := measurable_const.add (continuous_v.measurable.comp hH')
  have hf2 (y : ℝ) : |f y| ≤ 2 := abs_v_sum_le _ _
  have hg2 (y : ℝ) : |g y| ≤ 2 := abs_v_sum_le _ _
  have hfg (y : ℝ) : |f y-g y| ≤ 2*a := by
    have heq : f y-g y=(v (H x)-v (H' x))+(v (H y)-v (H' y)) := by dsimp [f,g]; ring
    rw [heq]
    exact (abs_add_le _ _).trans (by linarith [hv x,hv y])
  have hf_sq (y : ℝ) : |f y^2| ≤ 4 := by rw [abs_of_nonneg (sq_nonneg _)]; exact v_sum_sq_le _ _
  have hg_sq (y : ℝ) : |g y^2| ≤ 4 := by rw [abs_of_nonneg (sq_nonneg _)]; exact v_sum_sq_le _ _
  have he_sq (y : ℝ) : |f y^2-g y^2| ≤ 8*a := by
    have hh := abs_square_sub_le (by norm_num : (0:ℝ) ≤ 2) (hf2 y) (hg2 y) (hfg y)
    nlinarith only [hh]
  have he' := energy_error hb hr he (hf.pow_const 2) (hg.pow_const 2) hf_sq hg_sq he_sq
  have hb1 := (norm_components hb hr he).1
  have hp := bounded_pair_error hb hb1 hf hg hf2 hg2 (show 0 ≤ 2*a by positivity) hfg
  have hpf : |∫ y, b y*f y ∂μ| ≤ 2 := (field_pair_abs_le hb (memLp_bounded hf hf2) hb1).trans
    (l2Norm_le_bounded hf (by norm_num) hf2)
  have hpg : |∫ y, b y*g y ∂μ| ≤ 2 := (field_pair_abs_le hb (memLp_bounded hg hg2) hb1).trans
    (l2Norm_le_bounded hg (by norm_num) hg2)
  have hps := abs_square_sub_le (by norm_num : (0:ℝ) ≤ 2) hpf hpg hp
  rw [fieldRadicand_expansion hb hr hH,fieldRadicand_expansion hb hr hH']
  change |(∫ y, f y^2*(b y^2+r y^2) ∂μ)-(∫ y, f y*b y ∂μ)^2-
    ((∫ y, g y^2*(b y^2+r y^2) ∂μ)-(∫ y, g y*b y ∂μ)^2)| ≤ _
  simp_rw [mul_comm (f _) (b _),mul_comm (g _) (b _)]
  have heq : (∫ y, f y^2*(b y^2+r y^2) ∂μ)-(∫ y, b y*f y ∂μ)^2-
      ((∫ y, g y^2*(b y^2+r y^2) ∂μ)-(∫ y, b y*g y ∂μ)^2)=
      ((∫ y, f y^2*(b y^2+r y^2) ∂μ)-(∫ y, g y^2*(b y^2+r y^2) ∂μ))-
      ((∫ y, b y*f y ∂μ)^2-(∫ y, b y*g y ∂μ)^2) := by ring
  rw [heq]
  exact (abs_sub _ _).trans (by linarith only [he',hps])

lemma sqrt_fieldRadicand_error {b r H H' : ℝ → ℝ} (hb : MemLp b 2 μ) (hr : MemLp r 2 μ)
    (hH : Measurable H) (hH' : Measurable H')
    (he : (∫ x, b x^2+r x^2 ∂μ)=1) {a : ℝ} (ha : 0 ≤ a)
    (hv : ∀ x, |v (H x)-v (H' x)| ≤ a) (x : ℝ) :
    |sqrt (fieldRadicand μ H b r x)-sqrt (fieldRadicand μ H' b r x)| ≤ 4*sqrt a := by
  have hh := sqrt_difference (fieldRadicand_nonneg H b r x) (fieldRadicand_nonneg H' b r x)
    (fieldRadicand_error hb hr hH hH' he ha hv x)
  simpa only [sqrt_mul (by norm_num : (0:ℝ) ≤ 16),show sqrt (16:ℝ)=4 by norm_num] using hh

end SKRatio.Bins

end

end OAI
