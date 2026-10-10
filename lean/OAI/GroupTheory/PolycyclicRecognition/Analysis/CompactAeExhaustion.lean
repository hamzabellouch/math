import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.Compactness.LocallyCompact

namespace OAI

/-! # Extending local almost-everywhere assertions over an open domain -/

namespace PolycyclicRecognition

open Set MeasureTheory

theorem ae_restrict_of_compact_subsets
    {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [SecondCountableTopology X] [MeasurableSpace X]
    (μ : Measure X) (U : Set X) (hU : IsOpen U) (p : X → Prop)
    (h : ∀ K : Set X, IsCompact K → K ⊆ U → ∀ᵐ x ∂μ.restrict K, p x) :
    ∀ᵐ x ∂μ.restrict U, p x := by
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  have hσ : IsSigmaCompact U := by
    simpa only [Subtype.range_coe] using
      (isSigmaCompact_range (continuous_subtype_val : Continuous ((↑) : U → X)))
  obtain ⟨K, hK, hcover⟩ := hσ
  rw [← hcover, ae_restrict_iUnion_iff]
  intro n
  exact h (K n) (hK n) (fun x hx => hcover ▸ mem_iUnion.mpr ⟨n, hx⟩)

end PolycyclicRecognition

end OAI
