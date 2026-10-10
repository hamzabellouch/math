import OAI.Analysis.CircleDomains.Sobolev.SmoothMeanPeriodData
import OAI.Analysis.CircleDomains.Modulus.MeanPeriodBudget
import OAI.Analysis.CircleDomains.Selection.MeanPeriodCompatibility

namespace OAI

/-! The constructed smooth mean coordinate has the actual point-hit
budget and satisfies compatibility with every finite prior level union. -/

open Set Function Filter MeasureTheory Classical
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

omit [BorelSpace C(PathTime, Sphere)] in
theorem SmoothMeanPeriodData.incidence_le_hit
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (A : Set C(PathTime, Sphere)) (K : Set C(PathTime, ℂ))
    (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet) (η : ProbabilityMeasure A)
    (F : C(Sphere, ℂ)) (f : A → K) (hf : Measurable f)
    (hmap : ∀ γ : A, (f γ).val = F.comp γ.val)
    (G U S M : Set Sphere) (hU : IsOpen U) (hdense : Dense U) (b : Sphere)
    (hbS : b ∉ S) (hMS : M \ {b} ⊆ S)
    (h0 : ∀ x ∈ S, F x ≠ 0) (h1 : ∀ x ∈ M \ U, ‖F x‖ < 1)
    (hF : ∀ γ : A, InjOn F (range γ.val ∪ S))
    (π : Sphere → Sphere)
    (Q : SmoothMeanPeriodData hsch K hKS (η.map f) F G U S M b π) (x : Sphere) :
    volume {θ | (x, θ) ∈ periodBandGraph U M b Q.patch Q.branch} ≤
      if x = b then 1 else (η : Measure A) {γ | x ∈ range γ.val} := by
  classical
  exact mean_period_graph_incidence_le_hit hsch hsep A K hK hKS η F f hf hmap
    U M S hU hdense b h0 h1
    (fun x hx γ => (hF γ).mono (union_subset_union Subset.rfl
      (singleton_subset_iff.mpr (hMS ⟨hx.1, fun he => hx.2 (Or.inr he)⟩))))
    Q.patch Q.patch_open Q.patch_closure
    (fun i hi => hbS (Q.patch_closure i (subset_closure hi)))
    (hMS.trans Q.cover) Q.angle Q.bound Q.branch (fun i x _ => Q.bounded i x)
    Q.continuous Q.log_continuous Q.transition Q.error
    (fun x hx => (Q.error_vanishes x hx.2).mono_left nhdsWithin_le_nhds) Q.branch_value x

theorem SmoothMeanPeriodData.compatibility
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (hLusin : FiniteTorusAnalyticMeasurability)
    (π : Sphere → Sphere) (hπ : Continuous π) (hsurj : Surjective π)
    (hfiber : ∀ x, IsConnected (π ⁻¹' {x}))
    {G U Dust Flags S M : Set Sphere} (hG : IsOpen G)
    (hDust : IsCompact Dust) (hTD : IsTotallyDisconnected Dust) (hdust : π '' Gᶜ ⊆ Dust)
    (hU : IsSigmaCompact U) (hdense : Dense U) (hFlags : Flags.Countable)
    (hdisj : Disjoint U Flags) (b : Sphere) (hb : b ∈ Flags) (hbS : b ∉ S)
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
    (hF : ∀ γ : A, InjOn F (range γ.val ∪ S)) (hinj : InjOn F S)
    (hmiss : ∀ x ∈ (Uᶜ \ Flags) ∩ S, ∀ᵐ γ : A ∂(η : Measure A), x ∉ range γ.val)
    (Q : SmoothMeanPeriodData hsch K hKS (η.map f) F G U S M b π)
    (R : ℕ → Set (Sphere × UnitAddCircle)) (hR : ∀ i, IsClosed (R i))
    (hlength : ∀ i, ∀ᵐ t : UnitAddCircle ∂volume,
      (μH[1] : Measure Sphere) (G ∩ π ⁻¹' {x | (x, t) ∈ R i}) < ∞)
    (hgeneric : ∀ i, ∀ᵐ t : UnitAddCircle ∂volume,
      (∫⁻ γ, pathImageCount {x | (x, t) ∈ R i} γ
        ∂(μ : Measure C(PathTime, Sphere))) < ∞ ∧
      ∀ᵐ γ : C(PathTime, Sphere) ∂(μ : Measure C(PathTime, Sphere)),
        ¬ ∃ x ∈ range γ ∩ (Uᶜ \ Flags), (x, t) ∈ R i)
    (n : ℕ) (labels : Fin n → ℕ) :
    (volume.prod (Measure.pi (fun _ : Fin n => (volume : Measure UnitAddCircle))))
      (freeComponentFailure (Uᶜ \ Flags) (periodBandGraph U M b Q.patch Q.branch) R labels) = 0 := by
  have hWS : interior M \ {b} ⊆ S := fun x hx => hMS ⟨interior_subset hx.1, hx.2⟩
  exact mean_period_graph_compatibility hsch hsep hLusin π hπ hsurj hfiber hG
    hDust hTD hdust hU hdense hFlags hdisj b hb hboundary hMS harcs A K hK hKS η F f hf hmap
    μ ν hred hη h0 h1 (fun γ => (hF γ).mono (union_subset_union Subset.rfl hWS))
    (hinj.mono hWS)
    (fun x hx => mapped_arc_point_avoidance A K η F f hf hmap x
      (fun γ => (hF γ).mono (union_subset_union Subset.rfl (singleton_subset_iff.mpr hx.2)))
      (hmiss x hx))
    Q.patch Q.patch_open Q.patch_closure
    (fun i hi => hbS (Q.patch_closure i (subset_closure hi))) (hMS.trans Q.cover)
    Q.angle Q.bound Q.branch (fun i x _ => Q.bounded i x) Q.log_continuous Q.transition
    Q.error (fun x hx => (Q.error_vanishes x hx.1).mono_left nhdsWithin_le_nhds)
    Q.branch_value Q.closed R hR hlength hgeneric n labels

end CircleDomainRigidity

end

end OAI
