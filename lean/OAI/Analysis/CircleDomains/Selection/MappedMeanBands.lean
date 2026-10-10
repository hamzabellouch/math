import OAI.Analysis.CircleDomains.Selection.MeanIndexBands
import OAI.Analysis.CircleDomains.Selection.LiftedMeanContinuity

namespace OAI

/-! The mean-index band bound in the original path law. Injectivity of
the actual Jordan coordinate identifies the hit event exactly. -/

open Set Function Filter MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]
  [MeasurableSpace C(PathTime, X)]

 theorem mapped_arc_hit_probability_eq
    (A : Set C(PathTime, X)) (K : Set C(PathTime, ℂ)) (η : ProbabilityMeasure A)
    (F : C(X, ℂ)) (f : A → K) (hf : Measurable f)
    (hmap : ∀ γ : A, (f γ).val = F.comp γ.val)
    (x : X) (hF : ∀ γ : A, InjOn F (range γ.val ∪ {x})) :
    ((η.map f : ProbabilityMeasure K) : Measure K).real {γ | F x ∈ range γ.val} =
      (η : Measure A).real {γ | x ∈ range γ.val} := by
  have hH : MeasurableSet {γ : K | F x ∈ range γ.val} :=
    (isClosed_paths_hitting (F x)).measurableSet.preimage measurable_subtype_coe
  have he : f ⁻¹' {γ : K | F x ∈ range γ.val} = {γ : A | x ∈ range γ.val} := by
    ext γ
    change F x ∈ range (f γ).val ↔ x ∈ range γ.val
    rw [hmap γ]
    constructor
    · rintro ⟨t, ht⟩
      exact ⟨t, hF γ (Or.inl (mem_range_self t)) (Or.inr (mem_singleton x)) ht⟩
    · rintro ⟨t, ht⟩
      exact ⟨t, congrArg F ht⟩
  rw [measureReal_def, ProbabilityMeasure.toMeasure_map, Measure.map_apply hf hH, he,
    measureReal_def]

 theorem mapped_meanGeometricIndex_band_width
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (A : Set C(PathTime, X)) (K : Set C(PathTime, ℂ))
    (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet) (η : ProbabilityMeasure A)
    (F : C(X, ℂ)) (f : A → K) (hf : Measurable f)
    (hmap : ∀ γ : A, (f γ).val = F.comp γ.val)
    (x : X) (hF : ∀ γ : A, InjOn F (range γ.val ∪ {x}))
    {Y : Type*} [TopologicalSpace Y] (S : Set Y) (s : Y) (hs : s ∈ closure S)
    (L : Y → ClosedUpperHalfPlane) (hL : ContinuousWithinAt L S s)
    (hz : 0 < (L s).val.im) (hproj : diskRayProjection (L s).val = F x) :
    limsup (fun y => meanGeometricIndex hsch K hKS (η.map f) (L y)) (𝓝[S] s) -
      liminf (fun y => meanGeometricIndex hsch K hKS (η.map f) (L y)) (𝓝[S] s) ≤
        (η : Measure A).real {γ | x ∈ range γ.val} := by
  have hb := meanGeometricIndex_band_width hsch hsep K hK hKS (η.map f) S s hs L hL hz
  rw [hproj, mapped_arc_hit_probability_eq A K η F f hf hmap x hF] at hb
  exact hb

end CircleDomainRigidity

end

end OAI
