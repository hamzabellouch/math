import OAI.Geometry.SurfaceImmersion.Geometry.BoundaryJetPositivity

namespace OAI

/-! Both ordered boundary inequalities persist under small exterior C2 changes. -/
noncomputable section
open Set Filter
open scoped ContDiff Matrix Topology
namespace ClosedSurfaceR4.GeometryPreservation
open SmallModes RealModes NormalFrame VelocityFrame

def boundaryJetCrossings : Set (BoundaryProfile × (Base × (Base × ℝ))) :=
  {a | NormalFrame.gramDet (a.1 0) (a.1 1) ≠ 0 ∧
    boundaryJetSecond a.1 a.2.1 a.2.1 ≠ 0 ∧
    boundaryJetSecond a.1 a.2.2.1 a.2.2.1 ≠ 0 ∧
    0 < boundaryJetCrossing a.1 a.2.1 a.2.2.1 a.2.2.2 ∧
    0 < boundaryJetCrossing a.1 a.2.2.1 a.2.1 a.2.2.2}

lemma isOpen_boundaryJetCrossings : IsOpen boundaryJetCrossings := by
  apply isOpen_iff_mem_nhds.mpr
  intro a ha
  let Z := BoundaryProfile × (Base × (Base × ℝ))
  have hd : Continuous (fun a : Z => NormalFrame.gramDet (a.1 0) (a.1 1)) :=
    contDiff_gram_pair.continuous.comp (show Continuous (fun a : Z => (a.1 0,a.1 1)) by
      dsimp [Z]
      fun_prop)
  have hm : Continuous (fun a : Z => (a.1,a.2.1,a.2.1)) := by fun_prop
  have hn : Continuous (fun a : Z => (a.1,a.2.2.1,a.2.2.1)) := by fun_prop
  have hP := (continuousAt_boundaryJetSecond a.2.1 a.2.1 ha.1).comp
    (f := fun a : Z => (a.1,a.2.1,a.2.1)) (x := a) hm.continuousAt
  have hQ := (continuousAt_boundaryJetSecond a.2.2.1 a.2.2.1 ha.1).comp
    (f := fun a : Z => (a.1,a.2.2.1,a.2.2.1)) (x := a) hn.continuousAt
  have hc := continuousAt_boundaryJetCrossing (w := a.2.2.1) (κ := a.2.2.2) ha.1 ha.2.1
  have hswap : Continuous (fun a : Z => (a.1,a.2.2.1,a.2.1,a.2.2.2)) := by fun_prop
  have hr := (continuousAt_boundaryJetCrossing (w := a.2.1) (κ := a.2.2.2) ha.1 ha.2.2.1).comp
    (f := fun a : Z => (a.1,a.2.2.1,a.2.1,a.2.2.2)) (x := a) hswap.continuousAt
  filter_upwards [hd.continuousAt.eventually_ne ha.1,hP.eventually_ne ha.2.1,
    hQ.eventually_ne ha.2.2.1,hc.eventually (isOpen_Ioi.mem_nhds ha.2.2.2.1),
    hr.eventually (isOpen_Ioi.mem_nhds ha.2.2.2.2)] with b hb hP hQ hc hr
  exact ⟨hb,hP,hQ,hc,hr⟩

theorem compact_boundary_jet_crossings {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {J : X → BoundaryProfile} {v w : X → Base} {κ : X → ℝ}
    (hJ : Continuous J) (hv : Continuous v) (hw : Continuous w) (hκ : Continuous κ)
    (hold : ∀ x, (J x,v x,w x,κ x) ∈ boundaryJetCrossings) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : X, ∀ H : BoundaryProfile,
      ‖H-J x‖ < δ → (H,v x,w x,κ x) ∈ boundaryJetCrossings := by
  let f := fun x => (J x,v x,w x,κ x)
  have hf : Continuous f := hJ.prodMk (hv.prodMk (hw.prodMk hκ))
  obtain ⟨δ,hδ,hsub⟩ := (isCompact_range hf).exists_cthickening_subset_open
    isOpen_boundaryJetCrossings (by rintro _ ⟨x,rfl⟩; exact hold x)
  refine ⟨δ,hδ,?_⟩
  intro x H hH
  apply hsub
  apply Metric.thickening_subset_cthickening
  apply Metric.mem_thickening_iff.mpr
  refine ⟨f x,mem_range_self x,?_⟩
  change dist (H,(v x,w x,κ x)) (J x,(v x,w x,κ x)) < δ
  rwa [dist_prod_same_right,dist_eq_norm]

theorem compact_actual_exterior_crossings {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {F : RField 4} (hF : ContDiff ℝ ∞ F) {p : X → Base} {v w : X → Base} {κ : X → ℝ}
    (hp : Continuous p) (hv : Continuous v) (hw : Continuous w) (hκ : Continuous κ)
    (hD : ∀ x, NormalFrame.gramDet (coordDeriv dx F (p x)) (coordDeriv dy F (p x)) ≠ 0)
    (hP : ∀ x, realSecondForm F (v x) (v x) (p x) ≠ 0)
    (hQ : ∀ x, realSecondForm F (w x) (w x) (p x) ≠ 0)
    (hcross : ∀ x, 0 < orderedCrossing F (v x) (w x) (p x) (κ x) ∧
      0 < orderedCrossing F (w x) (v x) (p x) (κ x)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : X, ∀ G : RField 4, ContDiff ℝ ∞ G →
      ‖realBoundaryProfile G 1 (p x)-realBoundaryProfile F 1 (p x)‖ < δ →
      0 < orderedCrossing G (v x) (w x) (p x) (κ x) ∧
      0 < orderedCrossing G (w x) (v x) (p x) (κ x) := by
  have hJ : Continuous (fun x => realBoundaryProfile F 1 (p x)) :=
    (realBoundaryProfile_smooth hF 1).continuous.comp hp
  obtain ⟨δ,hδ,hclose⟩ := compact_boundary_jet_crossings hJ hv hw hκ (by
    intro x
    refine ⟨hD x,?_,?_,?_,?_⟩
    · rw [boundaryJetSecond_actual hF]; exact hP x
    · rw [boundaryJetSecond_actual hF]; exact hQ x
    · rw [boundaryJetCrossing_actual hF]; exact (hcross x).1
    · rw [boundaryJetCrossing_actual hF]; exact (hcross x).2)
  refine ⟨δ,hδ,?_⟩
  intro x G hG hnear
  have hh := (hclose x (realBoundaryProfile G 1 (p x)) hnear).2.2.2
  simpa only [boundaryJetCrossing_actual hG] using hh

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
