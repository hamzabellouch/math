import OAI.Analysis.CircleDomains.Sobolev.WeakProbabilityMeasurability

namespace OAI

/-! A measurable embedding of point spaces induces a measurable embedding
of probability laws. Its image is exactly the laws supported on the point image. -/
open Set Function MeasureTheory
noncomputable section
namespace CircleDomainRigidity

lemma measurable_probability_map {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {f : A → B} (hf : Measurable f) :
    Measurable (fun μ : ProbabilityMeasure A => μ.map f) := by
  exact ((Measure.measurable_map f hf).comp measurable_subtype_coe).subtype_mk

lemma probability_map_leftInverse {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {f : A → B} {g : B → A} (hf : Measurable f) (hg : Measurable g) (h : LeftInverse g f) :
    LeftInverse (fun ν : ProbabilityMeasure B => ν.map g) (fun μ : ProbabilityMeasure A => μ.map f) := by
  intro μ
  apply ProbabilityMeasure.toMeasure_injective
  change ((μ : Measure A).map f).map g = (μ : Measure A)
  rw [Measure.map_map hg hf]
  have he : g ∘ f = id := funext h
  rw [he, Measure.map_id]

lemma range_probability_map {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [Nonempty A] {f : A → B} (hf : MeasurableEmbedding f) :
    range (fun μ : ProbabilityMeasure A => μ.map f) =
      {ν : ProbabilityMeasure B | (ν : Measure B) (range f)ᶜ = 0} := by
  ext ν
  constructor
  · rintro ⟨μ, rfl⟩
    change (μ : Measure A).map f (range f)ᶜ = 0
    rw [Measure.map_apply hf.measurable hf.measurableSet_range.compl]
    simp only [preimage_compl, preimage_range, compl_univ, measure_empty]
  · intro hν
    refine ⟨ν.map hf.invFun, ?_⟩
    apply ProbabilityMeasure.toMeasure_injective
    change ((ν : Measure B).map hf.invFun).map f = (ν : Measure B)
    rw [Measure.map_map hf.measurable hf.measurable_invFun]
    have ha : ∀ᵐ b ∂(ν : Measure B), b ∈ range f := by
      simpa only [mem_compl_iff, not_not] using measure_eq_zero_iff_ae_notMem.mp hν
    have he : (f ∘ hf.invFun) =ᵐ[(ν : Measure B)] id := by
      filter_upwards [ha] with b hb
      obtain ⟨a, rfl⟩ := hb
      change f (hf.invFun (f a)) = f a
      rw [hf.leftInverse_invFun a]
    rw [Measure.map_congr he, Measure.map_id]

lemma measurableEmbedding_probability_map {A B : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [Nonempty A]
    {f : A → B} (hf : MeasurableEmbedding f) :
    MeasurableEmbedding (fun μ : ProbabilityMeasure A => μ.map f) := by
  apply MeasurableEmbedding.of_measurable_inverse (measurable_probability_map hf.measurable)
  · rw [range_probability_map hf]
    exact ((Measure.measurable_coe hf.measurableSet_range.compl).comp measurable_subtype_coe)
      (measurableSet_singleton 0)
  · exact measurable_probability_map hf.measurable_invFun
  · exact probability_map_leftInverse hf.measurable hf.measurable_invFun hf.leftInverse_invFun

end CircleDomainRigidity

end

end OAI
