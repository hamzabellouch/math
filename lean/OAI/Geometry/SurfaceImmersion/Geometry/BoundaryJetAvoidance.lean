import OAI.Geometry.SurfaceImmersion.Geometry.BoundaryJetSecondForm
import OAI.Geometry.SurfaceImmersion.Geometry.SecondFormNormalFields

namespace OAI

/-! Exterior antipode exclusions are open conditions on the unscaled
second jet and the preferred normal. Compactness makes the tolerance uniform. -/
noncomputable section
open Set Filter
open scoped ContDiff Matrix Topology
namespace ClosedSurfaceR4.GeometryPreservation
open SmallModes RealModes NormalFrame VelocityFrame

def boundaryJetAvoidance : Set (BoundaryProfile × (Vec × Base)) :=
  {a | NormalFrame.gramDet (a.1 0) (a.1 1) ≠ 0 ∧
    boundaryJetSecond a.1 a.2.2 a.2.2 ≠ 0 ∧
    a.2.1 ≠ -normalize (boundaryJetSecond a.1 a.2.2 a.2.2)}

lemma isOpen_boundaryJetAvoidance : IsOpen boundaryJetAvoidance := by
  apply isOpen_iff_mem_nhds.mpr
  intro a ha
  let Z := BoundaryProfile × (Vec × Base)
  have hd : Continuous (fun a : Z => NormalFrame.gramDet (a.1 0) (a.1 1)) := by
    exact contDiff_gram_pair.continuous.comp (show Continuous (fun a : Z => (a.1 0,a.1 1)) by
      dsimp [Z]
      fun_prop)
  have hm : Continuous (fun a : Z => (a.1,a.2.2,a.2.2)) := by fun_prop
  have hP := (continuousAt_boundaryJetSecond a.2.2 a.2.2 ha.1).comp
    (f := fun a : Z => (a.1,a.2.2,a.2.2)) (x := a) hm.continuousAt
  have hnorm := (normalize_smoothAt contDiffAt_id ha.2.1).continuousAt.comp
    (f := fun a : Z => boundaryJetSecond a.1 a.2.2 a.2.2) (x := a) hP
  have hn : Continuous (fun a : Z => a.2.1) := by fun_prop
  have hne := (hn.continuousAt.sub hnorm.neg).eventually_ne (sub_ne_zero.mpr ha.2.2)
  filter_upwards [hd.continuousAt.eventually_ne ha.1,hP.eventually_ne ha.2.1,hne] with b hbD hbP hbn
  exact ⟨hbD,hbP,sub_ne_zero.mp hbn⟩

theorem compact_boundary_jet_avoidance {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {J : X → BoundaryProfile} {n : X → Vec} {v : X → Base}
    (hJ : Continuous J) (hn : Continuous n) (hv : Continuous v)
    (hold : ∀ x, (J x,n x,v x) ∈ boundaryJetAvoidance) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : X, ∀ H : BoundaryProfile, ∀ m : Vec,
      ‖H-J x‖ < δ → ‖m-n x‖ < δ → (H,m,v x) ∈ boundaryJetAvoidance := by
  let f := fun x => (J x,n x,v x)
  have hf : Continuous f := hJ.prodMk (hn.prodMk hv)
  obtain ⟨δ,hδ,hsub⟩ := (isCompact_range hf).exists_cthickening_subset_open
    isOpen_boundaryJetAvoidance (by rintro _ ⟨x,rfl⟩; exact hold x)
  refine ⟨δ,hδ,?_⟩
  intro x H m hH hm
  apply hsub
  apply Metric.thickening_subset_cthickening
  apply Metric.mem_thickening_iff.mpr
  refine ⟨f x,mem_range_self x,?_⟩
  change dist (H,(m,v x)) (J x,(n x,v x)) < δ
  rw [Prod.dist_eq,dist_prod_same_right,dist_eq_norm,dist_eq_norm]
  exact max_lt hH hm

theorem compact_actual_exterior_avoidance {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {F : RField 4} (hF : ContDiff ℝ ∞ F) {p : X → Base} {n : X → Vec} {v : X → Base}
    (hp : Continuous p) (hn : Continuous n) (hv : Continuous v)
    (hD : ∀ x, NormalFrame.gramDet (coordDeriv dx F (p x)) (coordDeriv dy F (p x)) ≠ 0)
    (hP : ∀ x, realSecondForm F (v x) (v x) (p x) ≠ 0)
    (havoid : ∀ x, n x ≠ -normalize (realSecondForm F (v x) (v x) (p x))) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : X, ∀ G : RField 4, ContDiff ℝ ∞ G → ∀ m : Vec,
      ‖realBoundaryProfile G 1 (p x)-realBoundaryProfile F 1 (p x)‖ < δ →
      ‖m-n x‖ < δ → realSecondForm G (v x) (v x) (p x) ≠ 0 ∧
        m ≠ -normalize (realSecondForm G (v x) (v x) (p x)) := by
  have hJ : Continuous (fun x => realBoundaryProfile F 1 (p x)) :=
    (realBoundaryProfile_smooth hF 1).continuous.comp hp
  obtain ⟨δ,hδ,hclose⟩ := compact_boundary_jet_avoidance hJ hn hv (by
    intro x
    refine ⟨hD x,?_,?_⟩ <;> rw [boundaryJetSecond_actual hF]
    · exact hP x
    · exact havoid x)
  refine ⟨δ,hδ,?_⟩
  intro x G hG m hnear hm
  have hh := hclose x (realBoundaryProfile G 1 (p x)) m hnear hm
  simpa only [boundaryJetSecond_actual hG] using hh.2

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
