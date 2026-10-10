import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace OAI

namespace CompanionFPP
open MeasureTheory ProbabilityTheory

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  {μ : Measure α} {ν : Measure β} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

lemma square_integral_le_integral_square {f : α → ℝ} (hf : MemLp f 2 μ) :
    (∫ x, f x ∂μ)^2 ≤ ∫ x, (f x)^2 ∂μ := by
  have h := variance_nonneg f μ
  rw [variance_eq_sub hf] at h
  simp only [Pi.pow_apply] at h
  linarith

theorem integral_independent_square_difference {f : α → ℝ} (hf : MemLp f 2 μ) :
    (∫ z : α × α, (f z.1-f z.2)^2 ∂μ.prod μ) = 2 * variance f μ := by
  have h₁ : MemLp (fun z : α × α => f z.1) 2 (μ.prod μ) :=
    hf.comp_measurePreserving measurePreserving_fst
  have h₂ : MemLp (fun z : α × α => f z.2) 2 (μ.prod μ) :=
    hf.comp_measurePreserving measurePreserving_snd
  simp only [sub_sq, mul_assoc]
  rw [integral_add (f := fun z : α × α => f z.1^2 - 2*(f z.1*f z.2)) (g := fun z => f z.2^2) (h₁.integrable_sq.sub ((h₁.integrable_mul h₂).const_mul 2)) h₂.integrable_sq,
    integral_sub (f := fun z : α × α => f z.1^2) (g := fun z => 2*(f z.1*f z.2)) h₁.integrable_sq ((h₁.integrable_mul h₂).const_mul 2)]
  simp only [integral_const_mul]
  rw [integral_prod_mul, integral_fun_fst (f := fun x => (f x)^2), integral_fun_snd (f := fun x => (f x)^2), variance_eq_sub hf]
  simp only [Pi.pow_apply]
  simp
  ring

lemma bounded_memLp_two {f : α → ℝ} (hf : Measurable f) (C : ℝ)
    (hC : ∀ x, |f x| ≤ C) : MemLp f 2 μ :=
  MemLp.of_bound hf.aestronglyMeasurable C (.of_forall (by simpa only [Real.norm_eq_abs] using hC))

lemma abs_integral_le_bound {f : α → ℝ} (C : ℝ) (hC : ∀ x, |f x| ≤ C) (_h0 : 0 ≤ C) :
    |∫ x, f x ∂μ| ≤ C := by
  simpa using
    norm_integral_le_of_norm_le_const (μ := μ) (f := f) (.of_forall (by simpa only [Real.norm_eq_abs] using hC))

theorem product_variance_decomposition {f : α × β → ℝ} (hf : Measurable f)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ z, |f z| ≤ C) :
    variance f (μ.prod ν) =
      (∫ x, variance (fun y => f (x,y)) ν ∂μ) +
        variance (fun x => ∫ y, f (x,y) ∂ν) μ := by
  let g := fun x => ∫ y, f (x,y) ∂ν
  have hfm := bounded_memLp_two (μ := μ.prod ν) hf C hC
  have hsm : ∀ x, MemLp (fun y => f (x,y)) 2 ν := fun x =>
    bounded_memLp_two (hf.comp (measurable_const.prodMk measurable_id)) C (fun y => hC (x,y))
  have hgm : Measurable g := hf.stronglyMeasurable.integral_prod_right'.measurable
  have hgb : ∀ x, |g x| ≤ C := fun x => abs_integral_le_bound C (fun y => hC (x,y)) hC0
  have hg := bounded_memLp_two (μ := μ) hgm C hgb
  have hv : (fun x => variance (fun y => f (x,y)) ν) =
      fun x => (∫ y, (f (x,y))^2 ∂ν) - (g x)^2 := by
    funext x
    exact variance_eq_sub (hsm x)
  rw [hv, integral_sub hfm.integrable_sq.integral_prod_left hg.integrable_sq,
    variance_eq_sub hfm, variance_eq_sub hg]
  have hi := integral_prod f (hfm.integrable (by norm_num))
  have hi2 := integral_prod (fun z => (f z)^2) hfm.integrable_sq
  change _ = _ - _ + (_ - _)
  simp only [Pi.pow_apply]
  rw [hi, hi2]
  dsimp [g]
  ring

theorem variance_integral_le_integral_variance {f : α × β → ℝ} (hf : Measurable f)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ z, |f z| ≤ C) :
    variance (fun x => ∫ y, f (x,y) ∂ν) μ ≤
      ∫ y, variance (fun x => f (x,y)) μ ∂ν := by
  let g := fun x => ∫ y, f (x,y) ∂ν
  let h := fun y => ∫ x, f (x,y) ∂μ
  have hfm := bounded_memLp_two (μ := μ.prod ν) hf C hC
  have hgm : Measurable g := hf.stronglyMeasurable.integral_prod_right'.measurable
  have hhm : Measurable h := hf.stronglyMeasurable.integral_prod_left'.measurable
  have hgb : ∀ x, |g x| ≤ C := fun x => abs_integral_le_bound C (fun y => hC (x,y)) hC0
  have hhb : ∀ y, |h y| ≤ C := fun y => abs_integral_le_bound C (fun x => hC (x,y)) hC0
  have hg := bounded_memLp_two (μ := μ) hgm C hgb
  have hh := bounded_memLp_two (μ := ν) hhm C hhb
  let D := fun z : α × β => f z - h z.2
  have hDm : Measurable D := hf.sub (hhm.comp measurable_snd)
  have hDb : ∀ z, |D z| ≤ 2*C := by
    intro z
    exact (abs_sub _ _).trans (by linarith [hC z, hhb z.2])
  have hD := bounded_memLp_two (μ := μ.prod ν) hDm (2*C) hDb
  have hmean : (∫ y, h y ∂ν) = ∫ x, g x ∂μ :=
    (integral_integral_swap (f := fun x y => f (x,y)) (hfm.integrable (by norm_num))).symm
  have he : ∀ x, (∫ y, D (x,y) ∂ν) = g x - ∫ z, g z ∂μ := by
    intro x
    dsimp [D]
    rw [integral_sub (f := fun y => f (x,y)) (g := h) ((bounded_memLp_two (hf.comp (measurable_const.prodMk measurable_id))
      C (fun y => hC (x,y))).integrable (by norm_num)) (hh.integrable (by norm_num)), hmean]
  have hp : ∀ x, (g x - ∫ z, g z ∂μ)^2 ≤ ∫ y, (D (x,y))^2 ∂ν := by
    intro x
    rw [← he x]
    exact square_integral_le_integral_square
      (bounded_memLp_two (hDm.comp (measurable_const.prodMk measurable_id)) (2*C)
        (fun y => hDb (x,y)))
  rw [variance_eq_integral hgm.aemeasurable]
  apply (integral_mono (hg.sub (memLp_const _)).integrable_sq
    hD.integrable_sq.integral_prod_left hp).trans_eq
  rw [integral_integral_swap (f := fun x y => (D (x,y))^2) hD.integrable_sq]
  apply integral_congr_ae
  exact .of_forall (fun y => (variance_eq_integral
    (hf.comp (measurable_id.prodMk measurable_const)).aemeasurable).symm)

theorem product_variance_le {f : α × β → ℝ} (hf : Measurable f)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ z, |f z| ≤ C) :
    variance f (μ.prod ν) ≤
      (∫ x, variance (fun y => f (x,y)) ν ∂μ) +
      (∫ y, variance (fun x => f (x,y)) μ ∂ν) := by
  rw [product_variance_decomposition (μ := μ) (ν := ν) hf hC0 hC]
  exact add_le_add le_rfl (variance_integral_le_integral_variance (μ := μ) (ν := ν) hf hC0 hC)

lemma measurable_section_variance {f : α × β → ℝ} (hf : Measurable f)
    {C : ℝ} (hC : ∀ z, |f z| ≤ C) :
    Measurable (fun x => variance (fun y => f (x,y)) ν) := by
  have he : (fun x => variance (fun y => f (x,y)) ν) =
      fun x => (∫ y, (f (x,y))^2 ∂ν) - (∫ y, f (x,y) ∂ν)^2 := by
    funext x
    exact variance_eq_sub (bounded_memLp_two
      (hf.comp (measurable_const.prodMk measurable_id)) C (fun y => hC (x,y)))
  rw [he]
  exact (hf.pow_const 2).stronglyMeasurable.integral_prod_right'.measurable.sub
    (hf.stronglyMeasurable.integral_prod_right'.measurable.pow_const 2)

lemma variance_le_bound_square {f : α → ℝ} (hf : Measurable f)
    {C : ℝ} (_hC0 : 0 ≤ C) (hC : ∀ x, |f x| ≤ C) : variance f μ ≤ C^2 := by
  have hm := bounded_memLp_two (μ := μ) hf C hC
  apply (variance_le_expectation_sq hf.aestronglyMeasurable).trans
  have h := integral_mono hm.integrable_sq (integrable_const (C^2))
    (fun x => show (f x)^2 ≤ C^2 by nlinarith [hC x, abs_le.mp (hC x)])
  simpa using h

lemma integrable_section_variance {f : α × β → ℝ} (hf : Measurable f)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ z, |f z| ≤ C) :
    Integrable (fun x => variance (fun y => f (x,y)) ν) μ := by
  apply (bounded_memLp_two (measurable_section_variance hf hC) (C^2) ?_).integrable
    (by norm_num)
  intro x
  rw [abs_of_nonneg (variance_nonneg _ _)]
  exact variance_le_bound_square (hf.comp (measurable_const.prodMk measurable_id))
    hC0 (fun y => hC (x,y))

end CompanionFPP

end OAI
