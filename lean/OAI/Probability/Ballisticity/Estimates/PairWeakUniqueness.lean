import Mathlib
import OAI.Probability.Ballisticity.Estimates.GridLinear

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

lemma weak_limit_of_tight_identification {E : Type*} [MetricSpace E] [CompleteSpace E]
    [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
    (μ : ℕ → ProbabilityMeasure E) (W : ProbabilityMeasure E)
    (ht : IsTightMeasureSet (Set.range (fun i => (μ i : Measure E))))
    (hid : ∀ (j : ℕ → ℕ), Tendsto j atTop atTop → ∀ V : ProbabilityMeasure E,
      Tendsto (μ ∘ j) atTop (𝓝 V) → V=W) : Tendsto μ atTop (𝓝 W) := by
  have hc : IsCompact (closure (Set.range μ)) := isCompact_closure_of_isTightMeasureSet (by
    convert ht using 1
    ext x
    simp)
  apply Filter.tendsto_of_subseq_tendsto
  intro j hj
  obtain ⟨V,hV,k,hk,hlim⟩ := hc.tendsto_subseq (fun n => subset_closure (Set.mem_range_self (j n)))
  have he := hid (j ∘ k) (hj.comp hk.tendsto_atTop) V hlim
  exact ⟨k,he ▸ hlim⟩

lemma pair_weak_tight {E F : Type*}
    [MetricSpace E] [CompleteSpace E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
    [MetricSpace F] [CompleteSpace F] [SecondCountableTopology F] [MeasurableSpace F] [BorelSpace F]
    (μ : ℕ → ProbabilityMeasure (E × F)) (W : ProbabilityMeasure E) (V : ProbabilityMeasure F)
    (hf : Tendsto (fun i => (μ i).map Prod.fst) atTop (𝓝 W))
    (hg : Tendsto (fun i => (μ i).map Prod.snd) atTop (𝓝 V)) :
    IsTightMeasureSet (Set.range (fun i => (μ i : Measure (E × F)))) := by
  apply IsTightMeasureSet.prodMk
  · convert weak_sequence_tight hf using 1
    ext M
    simp only [Set.mem_image,Set.mem_range,exists_exists_eq_and,Measure.fst]
    rfl
  · convert weak_sequence_tight hg using 1
    ext M
    simp only [Set.mem_image,Set.mem_range,exists_exists_eq_and,Measure.snd]
    rfl

end DirectionalTransience

end

end

end OAI
