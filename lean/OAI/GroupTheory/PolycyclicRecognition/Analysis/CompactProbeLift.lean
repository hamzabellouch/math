import OAI.GroupTheory.PolycyclicRecognition.Analysis.SupportedProbabilityRestriction
import OAI.GroupTheory.PolycyclicRecognition.Analysis.CellProfileRestriction

namespace OAI

/-! # Retained compact probes in the ambient product Haar coordinates -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Set

/-- The original normalized cell law, viewed on its carrying subtype. -/
def cellSubtypeProbability {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (C : Set X) (hC : MeasurableSet C)
    (hzero : μ C ≠ 0) (hfinite : μ C ≠ ⊤) : ProbabilityMeasure C :=
  supportedProbabilityRestriction (cellProbabilityMeasure μ C hzero hfinite)
    C hC (ae_mem_cellProbabilityMeasure μ C hC hzero hfinite)

/-- Returning a retained compact probe set from a carrying subtype to the
ambient space preserves its exact original probability mass. -/
theorem compact_supported_probe_image
    {X : Type*} [TopologicalSpace X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X]
    (μ : ProbabilityMeasure X) (carrying : Set X) (hc : MeasurableSet carrying)
    (hfull : ∀ᵐ x ∂(μ : Measure X), x ∈ carrying)
    (K : Set carrying) (hK : IsCompact K) :
    IsCompact (Subtype.val '' K) ∧ MeasurableSet (Subtype.val '' K) ∧
      Subtype.val '' K ⊆ carrying ∧
      (μ : Measure X) (Subtype.val '' K) =
        (supportedProbabilityRestriction μ carrying hc hfull : Measure carrying) K := by
  have hcompact : IsCompact (Subtype.val '' K : Set X) := hK.image continuous_subtype_val
  refine ⟨hcompact, hcompact.isClosed.measurableSet, ?_, ?_⟩
  · rintro x ⟨y, _, rfl⟩
    exact y.property
  · rw [← supportedProbabilityRestriction_map μ carrying hc hfull,
      Measure.map_apply measurable_subtype_coe hcompact.isClosed.measurableSet]
    rw [preimage_image_eq _ Subtype.val_injective]

theorem cellSubtypeProbability_compact_image
    {X : Type*} [TopologicalSpace X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) (C : Set X) (hC : MeasurableSet C)
    (hzero : μ C ≠ 0) (hfinite : μ C ≠ ⊤)
    (K : Set C) (hK : IsCompact K) :
    IsCompact (Subtype.val '' K) ∧ MeasurableSet (Subtype.val '' K) ∧
      Subtype.val '' K ⊆ C ∧
      (cellProbabilityMeasure μ C hzero hfinite : Measure X) (Subtype.val '' K) =
        (cellSubtypeProbability μ C hC hzero hfinite : Measure C) K :=
  compact_supported_probe_image (cellProbabilityMeasure μ C hzero hfinite) C hC
    (ae_mem_cellProbabilityMeasure μ C hC hzero hfinite) K hK

end PolycyclicRecognition

end

end OAI
