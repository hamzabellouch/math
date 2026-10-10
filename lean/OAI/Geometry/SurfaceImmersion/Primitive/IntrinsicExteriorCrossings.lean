import OAI.Geometry.SurfaceImmersion.Geometry.BoundaryJetCurvature
import OAI.Geometry.SurfaceImmersion.Primitive.BoundaryJetCrossings

namespace OAI

/-! Exterior C2 stability for both ordered crossings with the new
immersion's actual Gaussian curvature. -/
noncomputable section
open Set Filter
open scoped ContDiff Matrix Topology
namespace ClosedSurfaceR4.GeometryPreservation
open SmallModes RealModes NormalFrame VelocityFrame

def intrinsicBoundaryJetCrossings : Set (BoundaryProfile × (Base × Base)) :=
  {a | (a.1,a.2.1,a.2.2,boundaryJetCurvature a.1) ∈ boundaryJetCrossings}

lemma isOpen_intrinsicBoundaryJetCrossings : IsOpen intrinsicBoundaryJetCrossings := by
  apply isOpen_iff_mem_nhds.mpr
  intro a ha
  have hc := (continuousAt_boundaryJetCurvature ha.1).comp
    (f := fun b : BoundaryProfile × (Base × Base) => b.1) (x := a)
    continuous_fst.continuousAt
  have hm : ContinuousAt (fun b : BoundaryProfile × (Base × Base) =>
      (b.1,b.2.1,b.2.2,boundaryJetCurvature b.1)) a :=
    continuous_fst.continuousAt.prodMk
      ((continuous_fst.comp continuous_snd).continuousAt.prodMk
        ((continuous_snd.comp continuous_snd).continuousAt.prodMk hc))
  exact hm.eventually (isOpen_boundaryJetCrossings.mem_nhds ha)

theorem compact_intrinsic_boundary_crossings {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {J : X → BoundaryProfile} {v w : X → Base}
    (hJ : Continuous J) (hv : Continuous v) (hw : Continuous w)
    (hold : ∀ x, (J x,v x,w x) ∈ intrinsicBoundaryJetCrossings) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : X, ∀ H : BoundaryProfile,
      ‖H-J x‖ < δ → (H,v x,w x) ∈ intrinsicBoundaryJetCrossings := by
  let f := fun x => (J x,v x,w x)
  have hf : Continuous f := hJ.prodMk (hv.prodMk hw)
  obtain ⟨δ,hδ,hsub⟩ := (isCompact_range hf).exists_cthickening_subset_open
    isOpen_intrinsicBoundaryJetCrossings (by rintro _ ⟨x,rfl⟩; exact hold x)
  refine ⟨δ,hδ,?_⟩
  intro x H hH
  apply hsub
  apply Metric.thickening_subset_cthickening
  apply Metric.mem_thickening_iff.mpr
  refine ⟨f x,mem_range_self x,?_⟩
  change dist (H,(v x,w x)) (J x,(v x,w x)) < δ
  rwa [dist_prod_same_right,dist_eq_norm]

theorem compact_actual_intrinsic_crossings {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {F : RField 4} (hF : ContDiff ℝ ∞ F) {p : X → Base} {v w : X → Base}
    (hp : Continuous p) (hv : Continuous v) (hw : Continuous w)
    (hD : ∀ x, gramDet (coordDeriv dx F (p x)) (coordDeriv dy F (p x)) ≠ 0)
    (hP : ∀ x, realSecondForm F (v x) (v x) (p x) ≠ 0)
    (hQ : ∀ x, realSecondForm F (w x) (w x) (p x) ≠ 0)
    (hcross : ∀ x,
      let κ := coordinateGaussianCurvature (realMetric F dx dx) (realMetric F dx dy)
        (realMetric F dy dy) (p x)
      0 < orderedCrossing F (v x) (w x) (p x) κ ∧
        0 < orderedCrossing F (w x) (v x) (p x) κ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : X, ∀ G : RField 4, ContDiff ℝ ∞ G →
      ‖realBoundaryProfile G 1 (p x)-realBoundaryProfile F 1 (p x)‖ < δ →
      let κ := coordinateGaussianCurvature (realMetric G dx dx) (realMetric G dx dy)
        (realMetric G dy dy) (p x)
      0 < orderedCrossing G (v x) (w x) (p x) κ ∧
        0 < orderedCrossing G (w x) (v x) (p x) κ := by
  have hJ : Continuous (fun x => realBoundaryProfile F 1 (p x)) :=
    (realBoundaryProfile_smooth hF 1).continuous.comp hp
  obtain ⟨δ,hδ,hclose⟩ := compact_intrinsic_boundary_crossings hJ hv hw (by
    intro x
    change (realBoundaryProfile F 1 (p x),v x,w x,
      boundaryJetCurvature (realBoundaryProfile F 1 (p x))) ∈ boundaryJetCrossings
    rw [boundaryJetCurvature_actual hF _ (hD x)]
    refine ⟨hD x,?_,?_,?_,?_⟩
    · rw [boundaryJetSecond_actual hF]; exact hP x
    · rw [boundaryJetSecond_actual hF]; exact hQ x
    · rw [boundaryJetCrossing_actual hF]; exact (hcross x).1
    · rw [boundaryJetCrossing_actual hF]; exact (hcross x).2)
  refine ⟨δ,hδ,?_⟩
  intro x G hG hnear
  have hm := hclose x (realBoundaryProfile G 1 (p x)) hnear
  have hDG : gramDet (coordDeriv dx G (p x)) (coordDeriv dy G (p x)) ≠ 0 := hm.1
  have hh := hm.2.2.2
  rw [boundaryJetCurvature_actual hG _ hDG] at hh
  simpa only [boundaryJetCrossing_actual hG] using hh

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
