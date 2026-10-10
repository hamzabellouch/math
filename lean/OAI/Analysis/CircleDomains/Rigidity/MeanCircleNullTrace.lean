import OAI.Analysis.CircleDomains.Rigidity.MeanIndexNullTrace
import OAI.Analysis.CircleDomains.Topology.MeanIndexCircle
import OAI.Analysis.CircleDomains.Transfer.LogarithmicCutCharts
import OAI.Analysis.CircleDomains.Probability.CircleNullImage

namespace OAI

/-! The actual circle-valued mean has Haar-null free traces on each
locally connected prior continuum. Two explicit argument cuts cover the
punctured mask, so no family of local branches is assumed. -/

open Set Function MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

theorem mean_circle_null_trace_on_continuum
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (A : Set C(PathTime, X)) (K : Set C(PathTime, ℂ)) (hK : IsCompact K)
    (hKS : K ⊆ diskTerminalArcSet) (η : ProbabilityMeasure A)
    (F : C(X, ℂ)) (f : A → K) (hf : Measurable f)
    (hmap : ∀ γ : A, (f γ).val = F.comp γ.val)
    {H S Free C : Set X} (hH : IsClosed H) (hS : IsOpen S)
    (hFree : MeasurableSet Free)
    (hmiss : ∀ᵐ γ : A ∂(η : Measure A), Disjoint (range γ.val ∩ H) Free)
    (hC : IsCompact C) (hCH : C ⊆ H) [LocallyConnectedSpace C]
    (harcs : HasSimpleArcsInConnectedOpens C)
    (hfinite : (∫⁻ γ, pathImageCount H γ
      ∂((η.map Subtype.val : ProbabilityMeasure C(PathTime, X)) : Measure _)) < ∞)
    (h0 : ∀ x ∈ S, F x ≠ 0) (h1 : ∀ x ∈ S, ‖F x‖ ≤ 1)
    (hF : ∀ γ : A, InjOn F (range γ.val ∪ S)) (hinj : InjOn F S) :
    volume ((fun x => diskMeanCircle hsch K hKS (η.map f) (F x)) ''
      (Free ∩ C ∩ S)) = 0 := by
  let W : ℝ → Set X := logarithmicCutDomain F S
  let Ψ : ℝ → X → ℂ := fun a x => logarithmicCutChart a (F x)
  let u : ℝ → X → ℝ := fun a x =>
    liftedMeanGeometricIndex hsch K hKS (η.map f) id (Ψ a x)
  let w : X → UnitAddCircle := fun x => diskMeanCircle hsch K hKS (η.map f) (F x)
  have hWS (a : ℝ) : W a ⊆ S := fun _ hx => hx.1
  have hWo (a : ℝ) : IsOpen (W a) :=
    isOpen_logarithmicCutDomain F F.continuous hS h0 a
  have hΨ (a : ℝ) : ContinuousOn (Ψ a) (W a) := by
    intro x hx
    exact ((continuousAt_logarithmicCutChart a (h0 x hx.1) hx.2).comp
      F.continuous.continuousAt).continuousWithinAt
  have hp (a : ℝ) (x : X) (hx : x ∈ W a) : 0 ≤ (Ψ a x).im :=
    logarithmicCutChart_nonneg a (h1 x hx.1)
  have hproj (a : ℝ) (x : X) (hx : x ∈ W a) : diskRayProjection (Ψ a x) = F x :=
    logarithmicCutChart_projection a (h0 x hx.1)
  have hlocal (a : ℝ) (x : X) (hx : x ∈ W a) : (u a x : UnitAddCircle) = w x := by
    dsimp only [u, w]
    rw [liftedMeanGeometricIndex_eq hsch K hKS (η.map f) id (Ψ a x) (hp a x hx),
      ← hproj a x hx]
    exact (diskMeanCircle_projection hsch hsep K hK hKS (η.map f) ⟨Ψ a x, hp a x hx⟩).symm
  have hn (a : ℝ) : volume (w '' (Free ∩ C ∩ W a)) = 0 := by
    have hreal := mean_index_null_trace_on_continuum hsch hsep A K hK hKS η F f hf
      hmap hH (hWo a) hFree hmiss hC hCH harcs hfinite (Ψ a) (hΨ a) (hp a)
      (hproj a) (fun γ => (hF γ).mono (union_subset_union_right _ (hWS a)))
      (hinj.mono (hWS a))
    apply measure_mono_null ?_ (volume_addCircle_image_eq_zero hreal)
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨u a x, ⟨x, hx, rfl⟩, hlocal a x hx.2⟩
  apply measure_mono_null ?_ (measure_union_null (hn 0) (hn (1 / 2)))
  rintro _ ⟨x, ⟨⟨hxF, hxC⟩, hxS⟩, rfl⟩
  rcases logarithmicCutDomain_cover F S hxS with hx | hx
  · exact Or.inl ⟨x, ⟨⟨hxF, hxC⟩, hx⟩, rfl⟩
  · exact Or.inr ⟨x, ⟨⟨hxF, hxC⟩, hx⟩, rfl⟩

end CircleDomainRigidity

end

end OAI
