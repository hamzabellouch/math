import OAI.Analysis.CircleDomains.Rigidity.MaskedCoordinateData
import OAI.Analysis.CircleDomains.Selection.MeanMarkedBranchBands

namespace OAI

/-! The actual mean of the chosen law supplies a masked coordinate,
including all marked bands and the original point-hit bound. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal ContDiff
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)]

theorem SmoothMeanPeriodData.exists_coordinate_data_with_norms
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (A : Set C(PathTime, Sphere)) (K : Set C(PathTime, ℂ))
    (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet) (η : ProbabilityMeasure A)
    (F : C(Sphere, ℂ)) (f : A → K) (hf : Measurable f)
    (hmap : ∀ γ : A, (f γ).val = F.comp γ.val)
    {G U S M : Set Sphere} (hG : IsOpen G) (hdense : Dense U)
    (hS : IsOpen S) (hM : IsClosed M) (hboundary : frontier M ⊆ U)
    {T : Type*} (σ : T → Sphere) (hσ : ∀ s, σ s ∉ U)
    (singular : T) (hbU : σ singular ∉ U)
    (hMS : M \ {σ singular} ⊆ S) (hbS : σ singular ∉ S)
    {π : Sphere → Sphere} (hπ : Continuous π)
    (hPU : ∀ z : ℂ, (z : Sphere) ∈ G → π (z : Sphere) ∈ U)
    (hfreeU : π '' Gᶜ ⊆ Uᶜ)
    (h0 : ∀ x ∈ S, F x ≠ 0) (h1 : ∀ x ∈ S, ‖F x‖ ≤ 1)
    (hstrict : ∀ x ∈ M \ U, ‖F x‖ < 1)
    (hF : ∀ γ : A, InjOn F (range γ.val ∪ S))
    (Q : SmoothMeanPeriodData hsch K hKS (η.map f) F G U S M (σ singular) π)
    (henergy : ∀ i : Fin 2, MemLp (fun x => circleFDeriv Q.euclidean x (EuclideanSpace.single i 1))
      2 (volume.restrict (planeSphere ⁻¹' (G ∩ π ⁻¹' S))))
    (hend : ∀ γ : A, σ singular ∈ range γ.val)
    (hbudget : Summable (fun s => ((η : Measure A).real {γ | σ s ∈ range γ.val}) ^ 2))
    (hmiss : ∀ x ∈ ((π '' Gᶜ) \ range σ) ∩ S,
      ∀ᵐ γ : K ∂(η.map f : Measure K), F x ∉ range γ.val) :
    ∃ C : MaskedCoordinateData G U π σ,
      C.graph = periodBandGraph U M (σ singular) Q.patch Q.branch ∧
      C.mask = M ∧ C.singular = singular ∧
      (∀ s, C.upper s - C.lower s ≤ (η : Measure A).real {γ | σ s ∈ range γ.val}) ∧
      (∀ z : ℂ, (z : Sphere) ∈ G → π (z : Sphere) ∈ S →
        C.physical (Complex.equivRealProdCLM z) = Q.physical z) ∧
      ∀ i : Fin 2, eLpNorm (fun x => circleFDeriv C.physical x
          (if i = 0 then (1, 0) else (0, 1))) 2
          (volume.restrict (realChartDomain G ∩ physicalMask π C.mask)) ≤
        eLpNorm (fun x => circleFDeriv Q.euclidean x (EuclideanSpace.single i 1))
          2 (volume.restrict (planeSphere ⁻¹' (G ∩ π ⁻¹' S))) := by
  obtain ⟨p, hmp, hdp, hsp, hEp, hpval, hpgraph, hpbranch, hpproj, hnorm⟩ :=
    Q.exists_masked_physical_data hsch hsep K hK hKS (η.map f) F hG hS hM hbU hMS hπ hPU
      h0 h1 henergy
  obtain ⟨lo, hi, hn, hhit, hsum, hband, hbranches⟩ :=
    Q.exists_marked_branch_band_family hsch hsep A K hK hKS η F f hf hmap hdense hMS hbS
      h0 hstrict hF σ hσ hend hbudget
  refine ⟨{
    graph := periodBandGraph U M (σ singular) Q.patch Q.branch
    graph_closed := Q.closed
    mask := M
    mask_closed := hM
    mask_frontier := hboundary
    singular := singular
    Index := Q.Index
    patch := Q.patch
    patch_open := Q.patch_open
    cover := hMS.trans Q.cover
    branch := Q.branch
    bound := Q.bound
    branch_bounded := Q.bounded
    physical := p
    measurable := hmp
    gradient_measurable := hdp
    smooth := hsp
    energy := hEp
    physical_graph := hpgraph
    branch_smooth := hpbranch
    branch_projection := hpproj
    lower := lo
    upper := hi
    width_nonneg := hn
    width_summable := hsum
    marked_fiber := hband
    marked_branch := hbranches
    free_fiber := ?_ }, rfl, rfl, rfl, hhit, hpval, ?_⟩
  · intro x hx hxr
    exact Q.free_fiber_subsingleton hsch hsep K hK hKS (η.map f) F hdense
      ((π '' Gᶜ) \ range σ) (fun x hx => hfreeU hx.1)
      (fun h => h.2 (mem_range_self singular)) hMS hbS h0 h1 hmiss ⟨hx, hxr⟩
  · intro i
    rw [← hnorm i]
    apply eLpNorm_mono_measure
    apply Measure.restrict_mono_set
    intro x hx
    refine ⟨hx.1, hMS ⟨hx.2, ?_⟩⟩
    intro heq
    exact hbU (heq ▸ hPU _ hx.1)

theorem SmoothMeanPeriodData.exists_coordinate_data
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (A : Set C(PathTime, Sphere)) (K : Set C(PathTime, ℂ))
    (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet) (η : ProbabilityMeasure A)
    (F : C(Sphere, ℂ)) (f : A → K) (hf : Measurable f)
    (hmap : ∀ γ : A, (f γ).val = F.comp γ.val)
    {G U S M : Set Sphere} (hG : IsOpen G) (hdense : Dense U)
    (hS : IsOpen S) (hM : IsClosed M) (hboundary : frontier M ⊆ U)
    {T : Type*} (σ : T → Sphere) (hσ : ∀ s, σ s ∉ U)
    (singular : T) (hbU : σ singular ∉ U)
    (hMS : M \ {σ singular} ⊆ S) (hbS : σ singular ∉ S)
    {π : Sphere → Sphere} (hπ : Continuous π)
    (hPU : ∀ z : ℂ, (z : Sphere) ∈ G → π (z : Sphere) ∈ U)
    (hfreeU : π '' Gᶜ ⊆ Uᶜ)
    (h0 : ∀ x ∈ S, F x ≠ 0) (h1 : ∀ x ∈ S, ‖F x‖ ≤ 1)
    (hstrict : ∀ x ∈ M \ U, ‖F x‖ < 1)
    (hF : ∀ γ : A, InjOn F (range γ.val ∪ S))
    (Q : SmoothMeanPeriodData hsch K hKS (η.map f) F G U S M (σ singular) π)
    (henergy : ∀ i : Fin 2, MemLp (fun x => circleFDeriv Q.euclidean x (EuclideanSpace.single i 1))
      2 (volume.restrict (planeSphere ⁻¹' (G ∩ π ⁻¹' S))))
    (hend : ∀ γ : A, σ singular ∈ range γ.val)
    (hbudget : Summable (fun s => ((η : Measure A).real {γ | σ s ∈ range γ.val}) ^ 2))
    (hmiss : ∀ x ∈ ((π '' Gᶜ) \ range σ) ∩ S,
      ∀ᵐ γ : K ∂(η.map f : Measure K), F x ∉ range γ.val) :
    ∃ C : MaskedCoordinateData G U π σ,
      C.graph = periodBandGraph U M (σ singular) Q.patch Q.branch ∧
      C.mask = M ∧ C.singular = singular ∧
      (∀ s, C.upper s - C.lower s ≤ (η : Measure A).real {γ | σ s ∈ range γ.val}) ∧
      ∀ z : ℂ, (z : Sphere) ∈ G → π (z : Sphere) ∈ S →
        C.physical (Complex.equivRealProdCLM z) = Q.physical z := by
  obtain ⟨C, hg, hm, hs, hw, hv, _⟩ := Q.exists_coordinate_data_with_norms
    hsch hsep A K hK hKS η F f hf hmap hG hdense hS hM hboundary σ hσ singular hbU hMS hbS
    hπ hPU hfreeU h0 h1 hstrict hF henergy hend hbudget hmiss
  exact ⟨C, hg, hm, hs, hw, hv⟩

end CircleDomainRigidity

end

end OAI
