import OAI.Analysis.CircleDomains.Selection.MeanPeriodFreeValues
import OAI.Analysis.CircleDomains.Topology.SubarcMeanCircleCompatibility
import OAI.Analysis.CircleDomains.Rigidity.MaskedLevelCompatibility

namespace OAI

/-! The actual masked mean-period graph satisfies ordered compatibility.
The boundary of the mask lies in the physical domain, so restricting to
its open interior loses no free incidences. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable {Y : Type*} [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y]
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

theorem mean_period_graph_compatibility
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (hLusin : FiniteTorusAnalyticMeasurability)
    (π : Y → Sphere) (hπ : Continuous π) (hsurj : Surjective π)
    (hfiber : ∀ x, IsConnected (π ⁻¹' {x}))
    {G : Set Y} (hG : IsOpen G) {Dust U Flags S M : Set Sphere}
    (hDust : IsCompact Dust) (hTD : IsTotallyDisconnected Dust) (hdust : π '' Gᶜ ⊆ Dust)
    (hU : IsSigmaCompact U) (hdense : Dense U) (hFlags : Flags.Countable)
    (hdisj : Disjoint U Flags) (b : Sphere) (hb : b ∈ Flags)
    (hboundary : M \ interior M ⊆ U) (hMS : M \ {b} ⊆ S)
    (harcs : ∀ C : Set Sphere, IsCompact C → LocallyConnectedSpace C →
      HasSimpleArcsInConnectedOpens C)
    (A : Set C(PathTime, Sphere)) (K : Set C(PathTime, ℂ)) (hK : IsCompact K)
    (hKS : K ⊆ diskTerminalArcSet) (η : ProbabilityMeasure A)
    (F : C(Sphere, ℂ)) (f : A → K) (hf : Measurable f)
    (hmap : ∀ γ : A, (f γ).val = F.comp γ.val)
    (μ ν : ProbabilityMeasure C(PathTime, Sphere)) (hred : IsSubarcLawReduction μ ν)
    (hη : η.map Subtype.val = ν)
    (h0 : ∀ x ∈ S, F x ≠ 0) (h1 : ∀ x ∈ S, ‖F x‖ ≤ 1)
    (hF : ∀ γ : A, InjOn F (range γ.val ∪ (interior M \ {b})))
    (hinj : InjOn F (interior M \ {b}))
    (hmiss : ∀ x ∈ (Uᶜ \ Flags) ∩ S, ∀ᵐ γ : K ∂((η.map f : ProbabilityMeasure K) : Measure K),
      F x ∉ range γ.val)
    {I : Type*} (V : I → Set Sphere) (hV : ∀ i, IsOpen (V i))
    (hVS : ∀ i, closure (V i) ⊆ S) (hbV : ∀ i, b ∉ V i)
    (hcover : M \ {b} ⊆ ⋃ i, V i)
    (a B : I → ℝ) (u : I → Sphere → ℝ)
    (hbound : ∀ i x, x ∈ U → |u i x| ≤ B i)
    (hlog : ∀ i, ContinuousOn (fun x => logarithmicCutChart (a i) (F x)) (closure (V i)))
    (htrans : ∀ i j x, x ∈ V i → x ∈ V j →
      ∃ k : ℤ, u j =ᶠ[𝓝[U] x] fun y => u i y + k)
    (error : Sphere → ℝ) (herror : ∀ x ∈ Uᶜ \ Flags, Tendsto error (𝓝[U] x) (𝓝 0))
    (hu : ∀ i x, x ∈ V i → u i x =
      meanGeometricIndex hsch K hKS (η.map f)
        (upperHalfPlaneClamp (logarithmicCutChart (a i) (F x))) + error x)
    (hclosed : IsClosed (periodBandGraph U M b V u))
    (R : ℕ → Set (Sphere × UnitAddCircle)) (hR : ∀ i, IsClosed (R i))
    (hlength : ∀ i, ∀ᵐ t : UnitAddCircle ∂volume,
      (μH[1] : Measure Y) (G ∩ π ⁻¹' {x | (x, t) ∈ R i}) < ∞)
    (hgeneric : ∀ i, ∀ᵐ t : UnitAddCircle ∂volume,
      (∫⁻ γ, pathImageCount {x | (x, t) ∈ R i} γ
        ∂(μ : Measure C(PathTime, Sphere))) < ∞ ∧
      ∀ᵐ γ : C(PathTime, Sphere) ∂(μ : Measure C(PathTime, Sphere)),
        ¬ ∃ x ∈ range γ ∩ (Uᶜ \ Flags), (x, t) ∈ R i)
    (n : ℕ) (labels : Fin n → ℕ) :
    (volume.prod (Measure.pi (fun _ : Fin n => (volume : Measure UnitAddCircle))))
      (freeComponentFailure (Uᶜ \ Flags) (periodBandGraph U M b V u) R labels) = 0 := by
  have hbfree : b ∉ Uᶜ \ Flags := fun hx => hx.2 hb
  have hWS : interior M \ {b} ⊆ S := fun x hx => hMS ⟨interior_subset hx.1, hx.2⟩
  have hsupport : ∀ x ∈ Uᶜ \ Flags, ∀ t, (x, t) ∈ periodBandGraph U M b V u →
      x ∈ interior M \ {b} := by
    intro x hx t ht
    refine ⟨?_, fun he => hx.2 (he ▸ hb)⟩
    by_contra hn
    exact hx.1 (hboundary ⟨ht.1, hn⟩)
  rw [← freeComponentFailure_inter_eq_of_support (Uᶜ \ Flags) (interior M \ {b})
    (periodBandGraph U M b V u) R labels hsupport]
  apply subarc_mean_circle_compatibility hsch hsep hLusin π hπ hsurj hfiber
    hG hDust hTD hdust hU hFlags hdisj (isOpen_interior.sdiff isClosed_singleton)
    harcs A K hK hKS η F f hf hmap μ ν hred hη
    (fun x hx => h0 x (hWS hx)) (fun x hx => h1 x (hWS hx)) hF hinj
    R hR hlength hgeneric (periodBandGraph U M b V u) hclosed _ n labels
  intro x hx t
  rw [period_graph_mean_free_value hsch hsep K hK hKS (η.map f) F U M S
    (Uᶜ \ Flags) hdense b hbfree h0 h1 hmiss V hV hVS hbV hcover a B u
    hbound hlog htrans error herror hu x hx.1 t]
  exact and_iff_right (interior_subset hx.2.1)

end CircleDomainRigidity

end

end OAI
