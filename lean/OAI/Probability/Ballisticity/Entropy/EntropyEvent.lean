import Mathlib
import OAI.Probability.Ballisticity.Entropy.EntropyVariational

namespace OAI

section

open MeasureTheory ProbabilityTheory InformationTheory Filter
open scoped ENNReal NNReal Classical Topology
namespace DirectionalTransience.Entropy
variable {X : Type*} [MeasurableSpace X]

lemma event_budget (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {C M t : ℝ} (hC : 0≤C) (hkl : klDiv μ ν≤ENNReal.ofReal C)
    (S : Set X) (hS : MeasurableSet S) (he : Real.exp t * ν.real S≤M) :
    μ.real S*t≤C+M := by
  let f : X → ℝ := S.indicator (fun _ => t)
  have hf : Measurable f := measurable_const.indicator hS
  have hb : ∃ B : ℝ, ∀ x, |f x|≤B := ⟨|t|,fun x => by
    by_cases hx : x∈S <;> simp [f,hx]⟩
  have hi : (∫ x, f x ∂μ)=μ.real S*t := by
    simp only [f,integral_indicator_const t hS,smul_eq_mul]
  have heq : (fun x => Real.exp (f x))=fun x => S.indicator (fun _ => Real.exp t-1) x+1 := by
    funext x
    by_cases hx : x∈S <;> simp [f,hx]
  have hh := expBudget_of_kl_le μ ν hC hkl f hf hb
  rw [hi,heq,integral_add ((integrable_const _).indicator hS) (integrable_const _),
    integral_indicator_const _ hS,integral_const,probReal_univ,one_smul,smul_eq_mul] at hh
  have hn : 0≤ν.real S := measureReal_nonneg
  nlinarith

lemma event_moment_budget (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {C : ℝ} (hC : 0≤C) (hkl : klDiv μ ν≤ENNReal.ofReal C)
    (F : X → ℝ≥0∞) (hF : Measurable F) {M : ℝ≥0∞} (hM : M≠⊤)
    (hmean : (∫⁻ x, F x ∂ν)≤M) (t : ℝ) :
    μ.real {x | ENNReal.ofReal (Real.exp t)≤F x}*t ≤ C+M.toReal := by
  have hm := (mul_meas_ge_le_lintegral hF (ENNReal.ofReal (Real.exp t))).trans hmean
  have hr := ENNReal.toReal_mono hM hm
  simp only [ENNReal.toReal_mul,ENNReal.toReal_ofReal (Real.exp_nonneg _)] at hr
  exact event_budget μ ν hC hkl _ (measurableSet_le measurable_const hF) hr

end DirectionalTransience.Entropy

end

end OAI
