import Mathlib

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem mean_ge_of_subGaussian_upper {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {f : Ω → ℝ} {v : NNReal}
    (hv : 0 < (v:ℝ))
    (hsg : HasSubgaussianMGF (fun x => f x-∫ y, f y ∂μ) v μ)
    {a B : ℝ} (hB : 0 ≤ B)
    (hp : Real.exp (-B) ≤ μ.real {x | a ≤ f x}) :
    a-Real.sqrt (2*(v:ℝ)*B) ≤ ∫ x, f x ∂μ := by
  by_cases h : a ≤ ∫ x, f x ∂μ
  · linarith [Real.sqrt_nonneg (2*(v:ℝ)*B)]
  have hd : 0 < a-∫ x, f x ∂μ := sub_pos.mpr (not_le.mp h)
  have ht := hsg.measure_ge_le hd.le
  have hevent : {x | a ≤ f x} = {x | a-(∫ y, f y ∂μ) ≤ f x-(∫ y, f y ∂μ)} := by
    ext x; simp only [Set.mem_ofPred_eq]; constructor <;> intro hx <;> linarith
  rw [← hevent] at ht
  have he := Real.exp_le_exp.mp (hp.trans ht)
  have hs : (a-(∫ y, f y ∂μ))^2 ≤ 2*(v:ℝ)*B := by
    have HH := (le_div_iff₀ (by positivity : 0 < 2*(v:ℝ))).mp
      (show -B ≤ -(a-(∫ y, f y ∂μ))^2/(2*(v:ℝ)) from he)
    nlinarith
  have hr := Real.sq_sqrt (show 0 ≤ 2*(v:ℝ)*B by positivity)
  have hrpos := Real.sqrt_nonneg (2*(v:ℝ)*B)
  nlinarith

theorem subGaussian_half_lower {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {f : Ω → ℝ} {v : NNReal}
    (hf : Measurable f) (hv : 0 < (v:ℝ))
    (hsg : HasSubgaussianMGF (fun x => f x-∫ y, f y ∂μ) v μ)
    {a B : ℝ} (hB : 0 ≤ B)
    (hp : Real.exp (-B) ≤ μ.real {x | a ≤ f x}) :
    (1/2:ℝ) ≤ μ.real {x | a-Real.sqrt (2*(v:ℝ)*B)-
      Real.sqrt (2*(v:ℝ)*Real.log 2) ≤ f x} := by
  have hm := mean_ge_of_subGaussian_upper hv hsg hB hp
  let u := Real.sqrt (2*(v:ℝ)*Real.log 2)
  have hu : 0 ≤ u := Real.sqrt_nonneg _
  have hu2 : u^2 = 2*(v:ℝ)*Real.log 2 :=
    Real.sq_sqrt (by positivity)
  have ht := hsg.neg.measure_ge_le hu
  simp only [Pi.neg_apply,neg_sub] at ht
  have hexp : Real.exp (-u^2/(2*(v:ℝ))) = (1/2:ℝ) := by
    rw [hu2]
    have hvn : (v:ℝ) ≠ 0 := hv.ne'
    have he : -(2*(v:ℝ)*Real.log 2)/(2*(v:ℝ)) = -Real.log 2 := by field_simp
    rw [he,Real.exp_neg,Real.exp_log (by norm_num)]
    norm_num
  rw [hexp] at ht
  let A := {x | a-Real.sqrt (2*(v:ℝ)*B)-u ≤ f x}
  have hA : MeasurableSet A := measurableSet_le measurable_const hf
  have hsub : Aᶜ ⊆ {x | u ≤ (∫ y, f y ∂μ)-f x} := by
    intro x hx
    have hx' : f x < a-Real.sqrt (2*(v:ℝ)*B)-u := not_le.mp hx
    simp only [Set.mem_ofPred_eq]
    linarith
  have hb := (measureReal_mono hsub).trans ht
  rw [measureReal_compl hA] at hb
  simp only [probReal_univ] at hb
  change (1/2:ℝ) ≤ μ.real A
  linarith
end SK.Analytic

end
end

end

end OAI
