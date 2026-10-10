import OAI.Analysis.CircleDomains.Sobolev.SmoothMeanPeriodConsequences

namespace OAI

/-! The actual smoothed mean has the local real-band width and free-fiber
properties used by mixed grid geometry. These are derived from its
retained correction and the original arc law. -/

open Set Function Filter MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)]

 theorem SmoothMeanPeriodData.branch_width_le_hit
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (A : Set C(PathTime, Sphere)) (K : Set C(PathTime, ℂ))
    (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet) (η : ProbabilityMeasure A)
    (F : C(Sphere, ℂ)) (f : A → K) (hf : Measurable f)
    (hmap : ∀ γ : A, (f γ).val = F.comp γ.val)
    {G U S M : Set Sphere} (hdense : Dense U) {b : Sphere} {π : Sphere → Sphere}
    (h0 : ∀ x ∈ S, F x ≠ 0) (h1 : ∀ x ∈ M \ U, ‖F x‖ < 1)
    (hF : ∀ γ : A, InjOn F (range γ.val ∪ S))
    (Q : SmoothMeanPeriodData hsch K hKS (η.map f) F G U S M b π)
    (i : Q.Index) {x : Sphere} (hx : x ∈ M \ U) (hxi : x ∈ Q.patch i) :
    limsup (Q.branch i) (𝓝[U] x) - liminf (Q.branch i) (𝓝[U] x) ≤
      (η : Measure A).real {γ | x ∈ range γ.val} := by
  have hxS : x ∈ S := Q.patch_closure i (subset_closure hxi)
  let L : Sphere → ClosedUpperHalfPlane := fun z =>
    upperHalfPlaneClamp (logarithmicCutChart (Q.angle i) (F z))
  have hLC : ContinuousAt L x := continuous_upperHalfPlaneClamp.continuousAt.comp
    ((Q.log_continuous i).continuousAt
      (mem_of_superset ((Q.patch_open i).mem_nhds hxi) subset_closure))
  have him : 0 < (logarithmicCutChart (Q.angle i) (F x)).im :=
    logarithmicCutChart_im_pos (Q.angle i) (h0 x hxS) (h1 x hx)
  have hLv : (L x).val = logarithmicCutChart (Q.angle i) (F x) :=
    upperHalfPlaneClamp_val him.le
  have hproj : diskRayProjection (L x).val = F x := by
    rw [hLv]
    exact logarithmicCutChart_projection (Q.angle i) (h0 x hxS)
  have heq : (fun z => Q.branch i z - meanGeometricIndex hsch K hKS (η.map f) (L z))
      =ᶠ[𝓝[U] x] Q.error := by
    filter_upwards [nhdsWithin_le_nhds ((Q.patch_open i).mem_nhds hxi)] with z hz
    rw [Q.branch_value i z hz]
    exact add_sub_cancel_left _ _
  have herr := ((Q.error_vanishes x hx.2).mono_left nhdsWithin_le_nhds).congr' heq.symm
  exact (perturbed_mapped_mean_bands hsch hsep A K hK hKS η F f hf hmap x
    (fun γ => (hF γ).mono (union_subset_union Subset.rfl (singleton_subset_iff.mpr hxS)))
    U x (by rw [hdense.closure_eq]; trivial) L hLC.continuousWithinAt
    (by simpa only [hLv] using him) hproj (Q.branch i) herr).2.2

omit [MeasurableSpace C(PathTime, Sphere)] in
 theorem SmoothMeanPeriodData.free_fiber_subsingleton
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (K : Set C(PathTime, ℂ)) (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet)
    (η : ProbabilityMeasure K) (F : C(Sphere, ℂ))
    {G U S M : Set Sphere} (hdense : Dense U) {b : Sphere} {π : Sphere → Sphere}
    (Q : SmoothMeanPeriodData hsch K hKS η F G U S M b π)
    (Free : Set Sphere) (hFree : Free ⊆ Uᶜ) (hb : b ∉ Free)
    (hMS : M \ {b} ⊆ S) (hbS : b ∉ S)
    (h0 : ∀ x ∈ S, F x ≠ 0) (h1 : ∀ x ∈ S, ‖F x‖ ≤ 1)
    (hmiss : ∀ x ∈ Free ∩ S, ∀ᵐ γ : K ∂(η : Measure K), F x ∉ range γ.val)
    {x : Sphere} (hx : x ∈ Free) :
    {θ : UnitAddCircle | (x, θ) ∈ periodBandGraph U M b Q.patch Q.branch}.Subsingleton := by
  have heq (θ : UnitAddCircle) := period_graph_mean_free_value hsch hsep K hK hKS η F
    U M S Free hdense b hb h0 h1 hmiss Q.patch Q.patch_open Q.patch_closure
    (fun i hi => hbS (Q.patch_closure i (subset_closure hi)))
    (hMS.trans Q.cover) Q.angle Q.bound Q.branch (fun i y _ => Q.bounded i y)
    Q.log_continuous Q.transition Q.error
    (fun y hy => (Q.error_vanishes y (hFree hy)).mono_left nhdsWithin_le_nhds)
    Q.branch_value x hx θ
  intro s hs t ht
  exact ((heq s).mp hs).2.symm.trans ((heq t).mp ht).2

end CircleDomainRigidity

end

end OAI
