import Mathlib

namespace OAI

section
section
noncomputable section
open Set Filter Manifold MeasureTheory Bundle Metric
open scoped Topology ContDiff ENNReal NNReal

namespace WeakMTWTransport

lemma aemeasurable_of_ae_continuousAt {X Y : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] [TopologicalSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] {μ : Measure X} {f : X → Y}
    (h : ∀ᵐ x ∂μ, ContinuousAt f x) : AEMeasurable f μ := by
  let s := {x | ContinuousAt f x}
  have hs : NullMeasurableSet s μ := .of_compl (.of_null (ae_iff.mp h))
  have hc : ContinuousOn f s := fun x hx => hx.continuousWithinAt
  have H := hc.aemeasurable₀ hs
  rw [Measure.restrict_eq_self_of_ae_mem (s := s) h] at H
  exact H

end WeakMTWTransport
end
end
end

end OAI
