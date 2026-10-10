import Mathlib

namespace OAI

universe uAlpha uBeta

/-! # Atomlessness of injective measurable pushforwards

This supports the standard-Borel-to-real reduction in the construction of
measure-preserving maps.
-/

open MeasureTheory

namespace Problem356

variable {α : Type uAlpha} {β : Type uBeta} [MeasurableSpace α] [MeasurableSpace β]

/-- An injective measurable map preserves the property of having null
singletons. No probability or finiteness hypothesis is needed. -/
theorem nullSingletonClass_map_of_injective (μ : Measure α)
    [NullSingletonClass μ] [MeasurableSingletonClass β]
    {f : α → β} (hf : Measurable f) (hinj : Function.Injective f) :
    NullSingletonClass (Measure.map f μ) := by
  constructor
  intro y
  rw [Measure.map_apply hf (measurableSet_singleton y)]
  have hsub : (f ⁻¹' {y}).Subsingleton := by
    intro x hx z hz
    apply hinj
    exact hx.trans hz.symm
  exact hsub.countable.measure_zero μ

/-- The real-valued measurable embedding used for standard Borel spaces
sends a singleton-null measure to a singleton-null real measure. -/
theorem nullSingletonClass_map_embeddingReal (μ : Measure α)
    [StandardBorelSpace α] [NullSingletonClass μ] :
    NullSingletonClass (Measure.map (embeddingReal α) μ) :=
  nullSingletonClass_map_of_injective μ (measurable_embeddingReal α)
    (measurableEmbedding_embeddingReal α).injective

end Problem356

end OAI
