import Mathlib
import OAI.Probability.SKRatio.Quantization.BinFunctional

namespace OAI

noncomputable section
open scoped NNReal ENNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real
namespace SKRatio.Bins
open Planted Scalar
variable {Ω α : Type*} [MeasurableSpace Ω] [Fintype α] [MeasurableSpace α]
  [MeasurableSingletonClass α] {μ : Measure Ω} [IsProbabilityMeasure μ]

def binMass (μ : Measure Ω) (σ : Ω → α) (a : α) : ℝ := μ.real {x | σ x=a}

def massRoot (μ : Measure Ω) (σ : Ω → α) (a : α) : ℝ := sqrt (binMass μ σ a)

def pullback (μ : Measure Ω) (σ : Ω → α) (B : α → ℝ) (x : Ω) : ℝ :=
  B (σ x)/massRoot μ σ (σ x)

lemma integral_finite_partition {σ : Ω → α} (hσ : Measurable σ) (f : α → ℝ) :
    (∫ x, f (σ x) ∂μ)=∑ a, binMass μ σ a*f a := by
  rw [←integral_map hσ.aemeasurable (measurable_of_countable f).aestronglyMeasurable,
    integral_fintype (by exact Integrable.of_finite)]
  apply Finset.sum_congr rfl
  intro a _
  rw [smul_eq_mul,map_measureReal_apply hσ (measurableSet_singleton a)]
  rfl

omit [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α] [IsProbabilityMeasure μ] in
lemma binMass_nonneg (σ : Ω → α) (a : α) : 0 ≤ binMass μ σ a := measureReal_nonneg

omit [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α] [IsProbabilityMeasure μ] in
lemma massRoot_sq (σ : Ω → α) (a : α) : massRoot μ σ a^2=binMass μ σ a :=
  sq_sqrt (binMass_nonneg σ a)

lemma sum_binMass {σ : Ω → α} (hσ : Measurable σ) : (∑ a, binMass μ σ a)=1 := by
  have hh := integral_finite_partition (μ := μ) hσ (fun _ => (1:ℝ))
  simpa only [mul_one,integral_const,probReal_univ,smul_eq_mul,one_mul] using hh.symm

lemma massRoot_unit {σ : Ω → α} (hσ : Measurable σ) : (∑ a, massRoot μ σ a^2)=1 := by
  simp_rw [massRoot_sq]
  exact sum_binMass hσ

lemma measurable_finite_comp {σ : Ω → α} (hσ : Measurable σ) (f : α → ℝ) :
    Measurable (fun x => f (σ x)) := (measurable_of_countable f).comp hσ

lemma memLp_finite_comp {σ : Ω → α} (hσ : Measurable σ) (f : α → ℝ) :
    MemLp (fun x => f (σ x)) 2 μ := by
  apply MemLp.of_bound (measurable_finite_comp hσ f).aestronglyMeasurable (∑ a, |f a|)
  exact ae_of_all _ (fun x => by
    rw [norm_eq_abs]
    exact Finset.single_le_sum (fun a _ => abs_nonneg (f a)) (Finset.mem_univ (σ x)))

omit [IsProbabilityMeasure μ] in
lemma measurable_pullback {σ : Ω → α} (hσ : Measurable σ) (B : α → ℝ) :
    Measurable (pullback μ σ B) := measurable_finite_comp hσ (fun a => B a / massRoot μ σ a)

lemma memLp_pullback {σ : Ω → α} (hσ : Measurable σ) (B : α → ℝ) :
    MemLp (pullback μ σ B) 2 μ := memLp_finite_comp hσ (fun a => B a / massRoot μ σ a)

omit [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α] [IsProbabilityMeasure μ] in
lemma massRoot_pos {σ : Ω → α} (hm : ∀ a, 0<binMass μ σ a) (a : α) : 0 < massRoot μ σ a :=
  sqrt_pos.mpr (hm a)

lemma integral_pullback {σ : Ω → α} (hσ : Measurable σ) (hm : ∀ a, 0<binMass μ σ a)
    (B f : α → ℝ) : (∫ x, pullback μ σ B x*f (σ x) ∂μ)=moment (massRoot μ σ) B f := by
  rw [show (fun x => pullback μ σ B x*f (σ x))=
    (fun x => (fun a => B a/massRoot μ σ a*f a) (σ x)) from rfl,
    integral_finite_partition (μ := μ) hσ (fun a => B a / massRoot μ σ a * f a)]
  unfold moment
  apply Finset.sum_congr rfl
  intro a _
  have hs := massRoot_sq (μ := μ) σ a
  have hn := (massRoot_pos hm a).ne'
  rw [←hs]
  field_simp

lemma integral_pullback_energy {σ : Ω → α} (hσ : Measurable σ)
    (hm : ∀ a, 0<binMass μ σ a) (B R f : α → ℝ) :
    (∫ x, f (σ x)*(pullback μ σ B x^2+pullback μ σ R x^2) ∂μ)=
      ∑ a, f a*(B a^2+R a^2) := by
  rw [show (fun x => f (σ x)*(pullback μ σ B x^2+pullback μ σ R x^2))=
    (fun x => (fun a => f a*((B a/massRoot μ σ a)^2+(R a/massRoot μ σ a)^2)) (σ x)) from rfl,
    integral_finite_partition (μ := μ) hσ (fun a => f a*((B a/massRoot μ σ a)^2+(R a/massRoot μ σ a)^2))]
  apply Finset.sum_congr rfl
  intro a _
  rw [div_pow,div_pow,massRoot_sq]
  field_simp [(hm a).ne']

lemma pullback_normalized [DecidableEq α] {σ : Ω → α} (hσ : Measurable σ)
    (hm : ∀ a, 0<binMass μ σ a) (z : Parameters α) :
    (∫ x, pullback μ σ (paramB z) x^2+pullback μ σ (paramR z) x^2 ∂μ)=1 := by
  simpa only [one_mul] using (integral_pullback_energy hσ hm (paramB z) (paramR z) (fun _ => 1)).trans
    (by simpa only [one_mul] using param_sum_sq z)

end SKRatio.Bins

end

end OAI
