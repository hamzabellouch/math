import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Restrict

namespace OAI

/-! A probability measure supported on a measurable set is the pushforward
of an actual probability measure on that set. -/

open Set Filter MeasureTheory

noncomputable section
namespace CircleDomainRigidity

 theorem exists_probability_on_support {X : Type*} [MeasurableSpace X]
    (μ : ProbabilityMeasure X) {K : Set X} (hK : MeasurableSet K)
    (hμ : ∀ᵐ x ∂(μ : Measure X), x ∈ K) :
    ∃ ν : ProbabilityMeasure K, ν.map Subtype.val = μ := by
  let ν : Measure K := (μ : Measure X).comap Subtype.val
  have hrestrict : (μ : Measure X).restrict K = μ :=
    Measure.restrict_eq_self_of_ae_mem hμ
  have hmap : ν.map Subtype.val = (μ : Measure X) := by
    change ((μ : Measure X).comap ((↑) : K → X)).map Subtype.val = _
    rw [map_comap_subtype_coe hK, hrestrict]
  have hprob : IsProbabilityMeasure ν := by
    constructor
    have he := congrArg (fun σ : Measure X => σ univ) hmap
    rw [Measure.map_apply measurable_subtype_coe MeasurableSet.univ, preimage_univ] at he
    exact he.trans (measure_univ : (μ : Measure X) univ = 1)
  refine ⟨⟨ν, hprob⟩, ?_⟩
  apply Subtype.ext
  exact hmap

variable {X : Type*} [MeasurableSpace X]

 def supportedProbability (μ : ProbabilityMeasure X) (A : Set X)
    (hA : MeasurableSet A) (hmem : ∀ᵐ x ∂(μ : Measure X), x ∈ A) : ProbabilityMeasure A :=
  ⟨(μ : Measure X).comap Subtype.val, ⟨by
    rw [(MeasurableEmbedding.subtype_coe hA).comap_apply, image_univ, Subtype.range_coe]
    exact (measure_congr (Filter.eventuallyEqSet_univ.mpr hmem)).trans (measure_univ)⟩⟩

 theorem supportedProbability_map (μ : ProbabilityMeasure X) (A : Set X)
    (hA : MeasurableSet A) (hmem : ∀ᵐ x ∂(μ : Measure X), x ∈ A) :
    (supportedProbability μ A hA hmem).map Subtype.val = μ := by
  apply ProbabilityMeasure.toMeasure_injective
  rw [ProbabilityMeasure.toMeasure_map]
  ext s hs
  rw [Measure.map_apply measurable_subtype_coe hs]
  change (μ : Measure X).comap Subtype.val (Subtype.val ⁻¹' s) = (μ : Measure X) s
  rw [(MeasurableEmbedding.subtype_coe hA).comap_apply]
  rw [image_preimage_eq_inter_range, Subtype.range_coe]
  apply measure_congr
  filter_upwards [hmem] with x hx
  simp only [mem_inter_iff, and_iff_left hx]


end CircleDomainRigidity

end

end OAI
