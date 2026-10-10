import Mathlib

namespace OAI

section
section
noncomputable section
open Set Filter MeasureTheory Metric Manifold Bundle
open scoped Topology ContDiff ENNReal NNReal BoundedContinuousFunction

namespace WeakMTWTransport

lemma exists_measurable_full_subset {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {P : X → Prop} (h : ∀ᵐ x ∂μ, P x) :
    ∃ G : Set X, MeasurableSet G ∧ (∀ᵐ x ∂μ, x∈G) ∧ ∀ x∈G, P x := by
  have hn : μ {x | ¬P x}=0 := ae_iff.mp h
  obtain ⟨G,hG,hGm,hGe⟩ := (NullMeasurableSet.of_null hn).compl.exists_measurable_subset_ae_eq
  refine ⟨G,hGm,?_,?_⟩
  · filter_upwards [hGe,h] with x hx hp
    exact hx.mpr (fun hn => hn hp)
  · intro x hx
    exact not_not.mp (hG hx)

end WeakMTWTransport
end
end
end

end OAI
