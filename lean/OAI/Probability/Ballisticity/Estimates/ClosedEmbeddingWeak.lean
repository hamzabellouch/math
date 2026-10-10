import Mathlib
import OAI.Probability.Ballisticity.Model

namespace OAI

section

open MeasureTheory TopologicalSpace Filter
open scoped Topology BoundedContinuousFunction
namespace DirectionalTransience.Entropy

lemma tendsto_of_map_closedEmbedding {X Y I : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] [NormalSpace Y]
    (e : X → Y) (he : Topology.IsClosedEmbedding e)
    {l : Filter I} {μs : I → ProbabilityMeasure X} {μ : ProbabilityMeasure X}
    (h : Tendsto (fun index => (μs index).map e) l
      (𝓝 (μ.map e))) : Tendsto μs l (𝓝 μ) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro f
  obtain ⟨g,_,hg⟩ := f.exists_extension_norm_eq_of_isClosedEmbedding he
  have ht := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp h g
  have hi (ρ : ProbabilityMeasure X) :
      (∫ y, g y ∂(ρ.map e : Measure Y))=
        ∫ x, f x ∂(ρ : Measure X) := by
    rw [ProbabilityMeasure.toMeasure_map,integral_map he.continuous.measurable.aemeasurable
      g.continuous.measurable.aestronglyMeasurable]
    exact congrArg (fun k : X → ℝ => ∫ x, k x ∂(ρ : Measure X)) hg
  simpa only [hi] using ht

end DirectionalTransience.Entropy

end

end OAI
