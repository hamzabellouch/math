import OAI.Analysis.CircleDomains.Selection.MappedMeanBands

namespace OAI

/-! Point avoidance passes to the actual compact disk-arc image law.
Injectivity is required only on each sampled arc together with the
single point under consideration. -/

open Set Function Filter MeasureTheory

noncomputable section
namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X] [MeasurableSpace C(PathTime, X)]

theorem mapped_arc_point_avoidance
    (A : Set C(PathTime, X)) (K : Set C(PathTime, ℂ)) (η : ProbabilityMeasure A)
    (F : C(X, ℂ)) (f : A → K) (hf : Measurable f)
    (hmap : ∀ γ : A, (f γ).val = F.comp γ.val)
    (x : X) (hF : ∀ γ : A, InjOn F (range γ.val ∪ {x}))
    (hmiss : ∀ᵐ γ : A ∂(η : Measure A), x ∉ range γ.val) :
    ∀ᵐ γ : K ∂((η.map f : ProbabilityMeasure K) : Measure K), F x ∉ range γ.val := by
  rw [ProbabilityMeasure.toMeasure_map]
  apply (ae_map_iff hf.aemeasurable ?_).mpr
  · filter_upwards [hmiss] with γ hγ
    rintro ⟨t, ht⟩
    apply hγ
    refine ⟨t, ?_⟩
    apply hF γ (Or.inl (mem_range_self t)) (Or.inr (mem_singleton x))
    simpa only [mem_preimage, hmap γ, ContinuousMap.comp_apply] using ht
  · exact ((isClosed_paths_hitting (F x)).measurableSet.preimage measurable_subtype_coe).compl

end CircleDomainRigidity

end

end OAI
