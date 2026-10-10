import OAI.Analysis.CircleDomains.Probability.MeasurableRangeSection
import OAI.Analysis.CircleDomains.Probability.FiniteMeasureCoordinates

namespace OAI

/-! Lift a probability supported on the image of a standard Borel code map.
A measurable range section and countable measure evaluations suffice
as a target encoding, with no probability-space topology hypothesis. -/
open Set Function MeasureTheory
noncomputable section
namespace CircleDomainRigidity

theorem exists_probability_lift_of_measurable_injection
    {A B Y : Type*} [MeasurableSpace A] [StandardBorelSpace A]
    [MeasurableSpace B] [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    [SecondCountableTopology Y]
    (K : A → B) (hK : Measurable K) (e : B → Y) (he : Measurable e)
    (hinj : Injective e) (η : ProbabilityMeasure B)
    (hrange : ∀ᵐ v ∂(η : Measure B), v ∈ range K) :
    ∃ P : ProbabilityMeasure A, P.map K = η := by
  have : Nonempty A := by
    obtain ⟨v, a, ha⟩ := hrange.exists
    exact ⟨a⟩
  obtain ⟨s, hs, hsection⟩ := exists_nullMeasurable_rangeSection
    (e ∘ K) (he.comp hK) ((η : Measure B).map e)
  have ht : AEMeasurable (s ∘ e) (η : Measure B) := hs.aemeasurable.comp_measurable he
  refine ⟨η.map (s ∘ e), ?_⟩
  apply ProbabilityMeasure.toMeasure_injective
  change ((η : Measure B).map (s ∘ e)).map K = (η : Measure B)
  rw [AEMeasurable.map_map_of_aemeasurable hK.aemeasurable ht]
  have hh : (K ∘ (s ∘ e)) =ᵐ[(η : Measure B)] id := by
    filter_upwards [hrange] with v hv
    apply hinj
    exact hsection (e v) (by obtain ⟨a, rfl⟩ := hv; exact mem_range_self a)
  rw [Measure.map_congr hh, Measure.map_id]

/-- The exact published probability-lifting input for finite-measure images. -/
theorem measurePlanLifting (A Z : Type*) [MeasurableSpace A] [StandardBorelSpace A]
    [TopologicalSpace Z] [PolishSpace Z] [MeasurableSpace Z] [BorelSpace Z] :
    MeasurePlanLifting A Z := by
  intro K hK η hrange
  let : MetricSpace (Finset ℕ → ENNReal) := TopologicalSpace.metrizableSpaceMetric _
  exact exists_probability_lift_of_measurable_injection K hK (finiteMeasureCoordinates Z)
    (measurable_finiteMeasureCoordinates Z) (injective_finiteMeasureCoordinates Z) η hrange

end CircleDomainRigidity

end

end OAI
