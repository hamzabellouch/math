import OAI.Analysis.CircleDomains.Modulus.MeanIndexArcPayment
import OAI.Analysis.CircleDomains.Probability.ArcNullImage

namespace OAI

/-! Null free traces for the actual averaged index on a locally connected
prior level continuum. Only connected-open arc existence is supplied by
the published topological input; the intersection measure and payment
inequality are constructed here. -/

open Set Function MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

theorem mean_index_null_trace_on_continuum
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (A : Set C(PathTime, X)) (K : Set C(PathTime, ℂ)) (hK : IsCompact K)
    (hKS : K ⊆ diskTerminalArcSet) (η : ProbabilityMeasure A)
    (F : C(X, ℂ)) (f : A → K) (hf : Measurable f)
    (hmap : ∀ γ : A, (f γ).val = F.comp γ.val)
    {H V Free C : Set X} (hH : IsClosed H) (hV : IsOpen V)
    (hFree : MeasurableSet Free)
    (hmiss : ∀ᵐ γ : A ∂(η : Measure A), Disjoint (range γ.val ∩ H) Free)
    (hC : IsCompact C) (hCH : C ⊆ H) [LocallyConnectedSpace C]
    (harcs : HasSimpleArcsInConnectedOpens C)
    (hfinite : (∫⁻ γ, pathImageCount H γ
      ∂((η.map Subtype.val : ProbabilityMeasure C(PathTime, X)) : Measure _)) < ∞)
    (Ψ : X → ℂ) (hΨ : ContinuousOn Ψ V)
    (hpos : ∀ x ∈ V, 0 ≤ (Ψ x).im)
    (hproj : ∀ x ∈ V, diskRayProjection (Ψ x) = F x)
    (hF : ∀ γ : A, InjOn F (range γ.val ∪ V)) (hinj : InjOn F V) :
    volume ((fun x => liftedMeanGeometricIndex hsch K hKS (η.map f) id (Ψ x)) ''
      (Free ∩ C ∩ V)) = 0 := by
  let u : X → ℝ := fun x => liftedMeanGeometricIndex hsch K hKS (η.map f) id (Ψ x)
  let ν := meanPathIntersectionMeasure H
    ((η.map Subtype.val : ProbabilityMeasure C(PathTime, X)) : Measure _)
  let : IsFiniteMeasure ν := meanPathIntersectionMeasure_finite H hH _ hfinite
  have hνFree : ν Free = 0 := by
    exact meanPathIntersectionMeasure_map_null (η : Measure A) Subtype.val
      measurable_subtype_coe H hH Free hFree hmiss
  let μC : Measure C := ν.comap Subtype.val
  have hemb : MeasurableEmbedding (Subtype.val : C → X) :=
    MeasurableEmbedding.subtype_coe hC.isClosed.measurableSet
  let : IsFiniteMeasure μC := ⟨by
    change ν.comap Subtype.val univ < ∞
    rw [hemb.comap_apply]
    exact measure_lt_top ν _⟩
  have hμFree : μC (Subtype.val ⁻¹' Free) = 0 := by
    rw [show μC (Subtype.val ⁻¹' Free) = ν (Subtype.val '' (Subtype.val ⁻¹' Free)) from
      hemb.comap_apply ν _]
    exact measure_mono_null (image_preimage_subset _ _) hνFree
  have hn : volume ((fun x : C => u x.val) ''
      ((Subtype.val ⁻¹' Free) ∩ (Subtype.val ⁻¹' V))) = 0 := by
    apply null_image_of_simple_arc_payment (μ := μC) harcs
      (hV.preimage continuous_subtype_val)
      (measure_mono_null inter_subset_left hμFree) (fun x : C => u x.val)
      (by norm_num : (0 : ℝ) ≤ 1)
    intro x hx y hy γ hγ hγV
    let α : Path x.val y.val := γ.map continuous_subtype_val
    have hα : Injective α := Subtype.val_injective.comp hγ
    have hαV : range α ⊆ V := by
      rintro z ⟨t, rfl⟩
      exact hγV (mem_range_self t)
    have hαH : range α ⊆ H := by
      rintro z ⟨t, rfl⟩
      exact hCH (γ t).property
    have hp := lifted_mean_index_arc_payment hsch hsep A K hK hKS η F f hf hmap
      hH hfinite Ψ hΨ hpos hproj hF hinj α.toContinuousMap hα hαV hαH
    have hr := (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top ν (range α))).mp hp
    have hmass : μC.real (range γ) = ν.real (range α) := by
      rw [measureReal_def, measureReal_def, hemb.comap_apply]
      congr 1
      apply congrArg ν
      change Subtype.val '' range γ = range (Subtype.val ∘ γ)
      exact (range_comp _ _).symm
    rw [one_mul, hmass]
    simpa [u, α, measureReal_def, abs_sub_comm] using hr
  have himage : (fun x : C => u x.val) ''
      ((Subtype.val ⁻¹' Free) ∩ (Subtype.val ⁻¹' V)) = u '' (Free ∩ C ∩ V) := by
    ext z
    constructor
    · rintro ⟨x, ⟨hxF, hxV⟩, rfl⟩
      exact ⟨x.val, ⟨⟨hxF, x.property⟩, hxV⟩, rfl⟩
    · rintro ⟨x, ⟨⟨hxF, hxC⟩, hxV⟩, rfl⟩
      exact ⟨⟨x, hxC⟩, ⟨hxF, hxV⟩, rfl⟩
  rwa [himage] at hn

end CircleDomainRigidity

end

end OAI
