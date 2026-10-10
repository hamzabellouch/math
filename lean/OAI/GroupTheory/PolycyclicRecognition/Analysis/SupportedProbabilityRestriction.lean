import OAI.GroupTheory.PolycyclicRecognition.Analysis.CompactProbabilityDensity

namespace OAI

/-! # Viewing a supported probability as a probability on its compact support -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Set Filter
open scoped Topology

/-- A probability carried by a measurable set, viewed on that subtype. -/
def supportedProbabilityRestriction
    {X : Type*} [MeasurableSpace X] (μ : ProbabilityMeasure X)
    (K : Set X) (hK : MeasurableSet K) (hfull : ∀ᵐ x ∂(μ : Measure X), x ∈ K) :
    ProbabilityMeasure K :=
  ⟨(μ : Measure X).comap Subtype.val, by
    constructor
    rw [comap_subtype_coe_apply hK, image_univ, Subtype.range_coe]
    have he := congrArg (fun m : Measure X => m univ)
      (Measure.restrict_eq_self_of_ae_mem hfull)
    simpa only [Measure.restrict_apply_univ, measure_univ] using he⟩

theorem supportedProbabilityRestriction_map
    {X : Type*} [MeasurableSpace X] (μ : ProbabilityMeasure X)
    (K : Set X) (hK : MeasurableSet K) (hfull : ∀ᵐ x ∂(μ : Measure X), x ∈ K) :
    Measure.map Subtype.val (supportedProbabilityRestriction μ K hK hfull : Measure K) = μ := by
  exact (map_comap_subtype_coe hK _).trans
    (Measure.restrict_eq_self_of_ae_mem hfull)

/-- Supported points stay supported after restriction to a carrying set. -/
theorem mem_support_supportedProbabilityRestriction
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    (μ : ProbabilityMeasure X) (K : Set X) (hK : MeasurableSet K)
    (hfull : ∀ᵐ x ∂(μ : Measure X), x ∈ K)
    {x : K} (hx : x.val ∈ (μ : Measure X).support) :
    x ∈ (supportedProbabilityRestriction μ K hK hfull : Measure K).support := by
  apply (Measure.mem_support_iff_forall x).mpr
  intro U hU
  rw [nhds_subtype_eq_comap] at hU
  obtain ⟨V, hV, hVU⟩ := Filter.mem_comap.mp hU
  have hp := (Measure.mem_support_iff_forall x.val).mp hx V hV
  have hsame : (μ : Measure X) (Subtype.val '' (Subtype.val ⁻¹' V : Set K)) =
      (μ : Measure X) V := by
    rw [image_preimage_eq_inter_range, Subtype.range_coe]
    apply measure_congr
    filter_upwards [hfull] with y hy
    simp only [mem_inter_iff, hy, and_true]
  have hsub : (supportedProbabilityRestriction μ K hK hfull : Measure K)
      (Subtype.val ⁻¹' V) = (μ : Measure X) V := by
    change (μ : Measure X).comap Subtype.val (Subtype.val ⁻¹' V) = _
    rw [comap_subtype_coe_apply hK, hsame]
  rw [← hsub] at hp
  exact hp.trans_le (measure_mono hVU)

/-- Restriction does not change integrals of ambient observables. -/
theorem integral_supportedProbabilityRestriction
    {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : ProbabilityMeasure X) (K : Set X) (hK : MeasurableSet K)
    (hfull : ∀ᵐ x ∂(μ : Measure X), x ∈ K) (f : X → E) :
    (∫ x : K, f x.val ∂(supportedProbabilityRestriction μ K hK hfull : Measure K)) =
      ∫ x, f x ∂(μ : Measure X) := by
  rw [show (supportedProbabilityRestriction μ K hK hfull : Measure K) =
    (μ : Measure X).comap Subtype.val from rfl,
    integral_subtype_comap hK, Measure.restrict_eq_self_of_ae_mem hfull]

end PolycyclicRecognition

end

end OAI
