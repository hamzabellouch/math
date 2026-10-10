import Mathlib
import OAI.Probability.SKRatio.Quantization.BinPartition
import OAI.Probability.SKRatio.Quantization.BinNet
import OAI.Probability.SKRatio.Variational.ScalarCoherent

namespace OAI

noncomputable section
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Real
namespace SKRatio.Bins
open Planted Scalar
variable {α : Type*} [Fintype α] [DecidableEq α]

omit [DecidableEq α] in
lemma finiteV_weight_tolerance (β : ℝ) (h : α → ℝ) {a : ℝ} (ha : 0<a) :
    ∃ δ : ℝ, 0<δ ∧ ∀ (t t' : WeightBox α) (z : Parameters α),
      (∀ d, |(t d:ℝ)-(t' d:ℝ)|<δ) →
      |finiteV β (fun d => t d) h z-finiteV β (fun d => t' d) h z|<a := by
  have hc : Continuous (fun q : WeightBox α × Parameters α =>
      finiteV β (fun d => q.1 d) h q.2) := by
    have ht : Continuous (fun q : WeightBox α × Parameters α =>
        fun d => (q.1 d : ℝ)) := continuous_pi (fun d =>
      continuous_subtype_val.comp ((continuous_apply d).comp continuous_fst))
    have hc' := (continuous_finiteV β h).comp (ht.prodMk
      (continuous_snd : Continuous (fun q : WeightBox α × Parameters α => q.2)))
    convert hc' using 1
    rfl
  obtain ⟨δ,hδ,hcont⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous hc) a ha
  refine ⟨δ,hδ,fun t t' z hh => ?_⟩
  apply hcont (a := (t,z)) (b := (t',z))
  simp only [Prod.dist_eq,dist_self,max_lt_iff]
  refine ⟨(dist_pi_lt_iff hδ).mpr ?_,hδ⟩
  intro d
  simpa only [Subtype.dist_eq,Real.dist_eq] using hh d

variable {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
  [MeasurableSingletonClass α] {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [DecidableEq α] in
lemma massRoot_le_one {σ : Ω → α} (hσ : Measurable σ) (a : α) : massRoot μ σ a≤1 := by
  have hs : massRoot μ σ a^2≤1 := by
    rw [←massRoot_unit (μ := μ) hσ]
    exact Finset.single_le_sum (fun d _ => sq_nonneg (massRoot μ σ d)) (Finset.mem_univ a)
  nlinarith only [hs]

def populationBox {σ : Ω → α} (hσ : Measurable σ) : WeightBox α :=
  fun a => ⟨massRoot μ σ a,sqrt_nonneg _,massRoot_le_one hσ a⟩

lemma finiteV_population_tolerance {σ : Ω → α} (hσ : Measurable σ)
    (β : ℝ) (h : α → ℝ) {a : ℝ} (ha : 0<a) :
    ∃ δ : ℝ, 0<δ ∧ ∀ {n : ℕ} (_ : 0<n) (τ : Fin n → α),
      (∀ d, |binT τ d-massRoot μ σ d|<δ) → ∀ z : Parameters α,
      finiteV β (binT τ) h z < finiteV β (massRoot μ σ) h z+a := by
  obtain ⟨δ,hδ,ht⟩ := finiteV_weight_tolerance β h ha
  refine ⟨δ,hδ,?_⟩
  intro n hn τ hh z
  have : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  have he := ht (binBox τ) (populationBox (μ := μ) hσ) z hh
  have hle := (le_abs_self _).trans_lt he
  change finiteV β (binT τ) h z-finiteV β (massRoot μ σ) h z<a at hle
  linarith only [hle]

end SKRatio.Bins

end

end OAI
