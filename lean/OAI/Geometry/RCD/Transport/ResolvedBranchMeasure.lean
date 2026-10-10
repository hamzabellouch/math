import OAI.Geometry.RCD.Transport.ResolvePathBranch

namespace OAI

/-! # Endpoint and compression control for the measurable branch splice -/

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology
noncomputable section
namespace RegularPointCoordinates

theorem map_le_add_of_choice {Ω Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Y]
    (μ : Measure Ω) {f g h : Ω → Y} (hf : Measurable f) (hg : Measurable g)
    (hh : Measurable h) (hc : ∀ x, h x=f x ∨ h x=g x) :
    μ.map h≤μ.map f+μ.map g := by
  apply Measure.le_iff.mpr
  intro A hA
  rw [Measure.add_apply,Measure.map_apply hh hA,Measure.map_apply hf hA,Measure.map_apply hg hA]
  apply (measure_mono ?_).trans (measure_union_le _ _)
  intro x hx
  rcases hc x with he | he
  · exact Or.inl (by simpa only [mem_preimage,he] using hx)
  · exact Or.inr (by simpa only [mem_preimage,he] using hx)

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [SeparableSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem resolved_branch_endpoints (q : Time) (σ : Measure (C(Time,X)×C(Time,X))) :
    (σ.map (resolvePathBranch q)).map (fun γ => (γ 0,γ 1))=
      (σ.map Prod.snd).map (fun γ => (γ 0,γ 1)) := by
  rw [Measure.map_map ((measurable_path_eval 0).prodMk (measurable_path_eval 1))
    (measurable_resolvePathBranch q),
    Measure.map_map ((measurable_path_eval 0).prodMk (measurable_path_eval 1)) measurable_snd]
  apply Measure.map_congr
  exact .of_forall fun z => Prod.ext (resolvePathBranch_zero q z) (resolvePathBranch_one q z)

theorem resolved_branch_endpoint_time (q : Time) (σ : Measure (C(Time,X)×C(Time,X)))
    (t : Time) (ht : t=0 ∨ t=1) :
    (σ.map (resolvePathBranch q)).map (fun γ => γ t)=
      (σ.map Prod.snd).map (fun γ => γ t) := by
  rw [Measure.map_map (measurable_path_eval t) (measurable_resolvePathBranch q),
    Measure.map_map (measurable_path_eval t) measurable_snd]
  apply Measure.map_congr
  apply Filter.Eventually.of_forall
  intro z
  rcases ht with rfl | rfl
  · exact resolvePathBranch_zero q z
  · exact resolvePathBranch_one q z

theorem resolved_branch_optimal (q : Time) (σ : Measure (C(Time,X)×C(Time,X)))
    (hp : IsOptimalCoupling ((σ.map Prod.snd).map (fun γ => γ 0))
      ((σ.map Prod.snd).map (fun γ => γ 1))
      ((σ.map Prod.snd).map (fun γ => (γ 0,γ 1)))) :
    IsOptimalCoupling ((σ.map (resolvePathBranch q)).map (fun γ => γ 0))
      ((σ.map (resolvePathBranch q)).map (fun γ => γ 1))
      ((σ.map (resolvePathBranch q)).map (fun γ => (γ 0,γ 1))) := by
  rw [resolved_branch_endpoint_time q σ 0 (Or.inl rfl),
    resolved_branch_endpoint_time q σ 1 (Or.inr rfl),resolved_branch_endpoints]
  exact hp

theorem resolved_branch_compression (q : Time) (σ : Measure (C(Time,X)×C(Time,X))) (t : Time) :
    (σ.map (resolvePathBranch q)).map (fun γ => γ t)≤
      (σ.map Prod.fst).map (fun γ => γ t)+(σ.map Prod.snd).map (fun γ => γ t) := by
  rw [Measure.map_map (measurable_path_eval t) (measurable_resolvePathBranch q),
    Measure.map_map (measurable_path_eval t) measurable_fst,
    Measure.map_map (measurable_path_eval t) measurable_snd]
  exact map_le_add_of_choice σ ((measurable_path_eval t).comp measurable_fst)
    ((measurable_path_eval t).comp measurable_snd)
    ((measurable_path_eval t).comp (measurable_resolvePathBranch q))
    (fun z => resolvePathBranch_choice q z t)

theorem resolved_branch_geodesic (q : Time) (σ : Measure (C(Time,X)×C(Time,X)))
    (hg : ∀ᵐ z ∂σ, IsGeodesic z.1 ∧ IsGeodesic z.2) :
    ∀ᵐ γ ∂σ.map (resolvePathBranch q), IsGeodesic γ := by
  apply (ae_map_iff (measurable_resolvePathBranch q).aemeasurable
    isClosed_geodesicSet.measurableSet).mpr
  exact hg.mono fun z hz => resolvePathBranch_isGeodesic q z hz.1 hz.2

omit [MeasurableSpace X] [BorelSpace X] [SeparableSpace X] in
theorem resolved_branch_common_past (q : Time) {z : C(Time,X)×C(Time,X)}
    {T : Time} (hT : T≤q) (hz : z∈pathAgreement (T:ℝ)) :
    ∀ r : Time, r≤T → z.1 r=resolvePathBranch q z r := by
  have h0 : z.1 0=z.2 0 := hz 0 T.property.1
  have hlast : T≤lastPathAgreement q z :=
    (lastPathAgreement_isGreatest q z).2 (Or.inr ⟨hT,hz T le_rfl⟩)
  intro r hr
  rw [resolvePathBranch_apply q z h0,ite_eq_left (hr.trans hlast)]

end RegularPointCoordinates

end

end OAI
