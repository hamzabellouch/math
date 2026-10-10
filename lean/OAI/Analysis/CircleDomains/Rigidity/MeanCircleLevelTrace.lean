import OAI.Analysis.CircleDomains.Rigidity.MeanCircleNullTrace
import OAI.Analysis.CircleDomains.Topology.LevelQuotient
import OAI.Analysis.CircleDomains.Selection.LusinInput

namespace OAI

/-! Finite physical length gives the topology of a prior level union.
The actual mean-index payment then makes its free component traces null. -/

open Set Function MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

theorem mean_circle_null_component_traces
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (π : Y → X) (hπ : Continuous π) (hsurj : Surjective π)
    (hfiber : ∀ x, IsConnected (π ⁻¹' {x}))
    {G : Set Y} (hG : IsOpen G) {B H Free S : Set X}
    (hB : IsCompact B) (hTD : IsTotallyDisconnected B) (hdust : π '' Gᶜ ⊆ B)
    (hH : IsCompact H) (hlength : (μH[1] : Measure Y) (π ⁻¹' H ∩ G) < ∞)
    (hFree : MeasurableSet Free) (hS : IsOpen S)
    (harcs : ∀ C : Set X, IsCompact C → LocallyConnectedSpace C →
      HasSimpleArcsInConnectedOpens C)
    (A : Set C(PathTime, X)) (K : Set C(PathTime, ℂ)) (hK : IsCompact K)
    (hKS : K ⊆ diskTerminalArcSet) (η : ProbabilityMeasure A)
    (F : C(X, ℂ)) (f : A → K) (hf : Measurable f)
    (hmap : ∀ γ : A, (f γ).val = F.comp γ.val)
    (hmiss : ∀ᵐ γ : A ∂(η : Measure A), Disjoint (range γ.val ∩ H) Free)
    (hfinite : (∫⁻ γ, pathImageCount H γ
      ∂((η.map Subtype.val : ProbabilityMeasure C(PathTime, X)) : Measure _)) < ∞)
    (h0 : ∀ x ∈ S, F x ≠ 0) (h1 : ∀ x ∈ S, ‖F x‖ ≤ 1)
    (hF : ∀ γ : A, InjOn F (range γ.val ∪ S)) (hinj : InjOn F S) :
    HasFiniteLargeContinuumBound H ∧
      ∀ C : Set H, (∃ x, C = connectedComponent x) → C.Nontrivial →
        volume ((fun x : H => diskMeanCircle hsch K hKS (η.map f) (F x.val)) ''
          ((Subtype.val ⁻¹' (Free ∩ S)) ∩ C)) = 0 := by
  obtain ⟨hbound, _, hloc⟩ := level_topology_of_finite_physical_length
    π hπ hsurj hfiber hG hB hTD hdust hH hlength
  refine ⟨hbound, ?_⟩
  let : CompactSpace H := isCompact_iff_compactSpace.mp hH
  rintro C ⟨x, rfl⟩ _
  let C := connectedComponent x
  have hC : IsCompact C := isClosed_connectedComponent.isCompact
  let : LocallyConnectedSpace C := hloc C hC isConnected_connectedComponent
  let D : Set X := Subtype.val '' C
  have hD : IsCompact D := hC.image continuous_subtype_val
  have hDH : D ⊆ H := by
    rintro _ ⟨z, _, rfl⟩
    exact z.property
  let e : C ≃ₜ D := Topology.IsEmbedding.subtypeVal.homeomorphImage C
  let : LocallyConnectedSpace D := e.symm.isOpenEmbedding.locallyConnectedSpace
  have hn := mean_circle_null_trace_on_continuum hsch hsep A K hK hKS η F f hf hmap
    hH.isClosed hS hFree hmiss hD hDH (harcs D hD inferInstance)
    hfinite h0 h1 hF hinj
  have himage : (fun z : H => diskMeanCircle hsch K hKS (η.map f) (F z.val)) ''
      ((Subtype.val ⁻¹' (Free ∩ S)) ∩ C) =
      (fun z => diskMeanCircle hsch K hKS (η.map f) (F z)) '' (Free ∩ D ∩ S) := by
    ext t
    constructor
    · rintro ⟨z, ⟨⟨hzF, hzS⟩, hzC⟩, rfl⟩
      exact ⟨z.val, ⟨⟨hzF, z, hzC, rfl⟩, hzS⟩, rfl⟩
    · rintro ⟨z, ⟨⟨hzF, y, hyC, rfl⟩, hzS⟩, rfl⟩
      exact ⟨y, ⟨⟨hzF, hzS⟩, hyC⟩, rfl⟩
  rwa [himage]

end CircleDomainRigidity

end

end OAI
