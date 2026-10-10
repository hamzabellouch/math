import OAI.Geometry.SurfaceImmersion.Geometry.BoundaryJetAvoidance

namespace OAI

/-! Uniform exterior preservation of the positive normal pairings. -/
noncomputable section
open Set Filter
open scoped ContDiff Matrix Topology
namespace ClosedSurfaceR4.GeometryPreservation
open SmallModes RealModes NormalFrame VelocityFrame

def boundaryJetPositivity : Set (BoundaryProfile × (Vec × Base)) :=
  {a | NormalFrame.gramDet (a.1 0) (a.1 1) ≠ 0 ∧
    0 < boundaryJetSecond a.1 a.2.2 a.2.2 ⬝ᵥ a.2.1}

lemma isOpen_boundaryJetPositivity : IsOpen boundaryJetPositivity := by
  apply isOpen_iff_mem_nhds.mpr
  intro a ha
  let Z := BoundaryProfile × (Vec × Base)
  have hd : Continuous (fun a : Z => NormalFrame.gramDet (a.1 0) (a.1 1)) :=
    contDiff_gram_pair.continuous.comp (show Continuous (fun a : Z => (a.1 0,a.1 1)) by
      dsimp [Z]
      fun_prop)
  have hm : Continuous (fun a : Z => (a.1,a.2.2,a.2.2)) := by fun_prop
  have hP := (continuousAt_boundaryJetSecond a.2.2 a.2.2 ha.1).comp
    (f := fun a : Z => (a.1,a.2.2,a.2.2)) (x := a) hm.continuousAt
  have hn : Continuous (fun a : Z => a.2.1) := by fun_prop
  have hdot : Continuous (fun p : Vec × Vec => p.1 ⬝ᵥ p.2) := by
    unfold dotProduct
    fun_prop
  have hh := hdot.continuousAt.comp (f := fun a : Z =>
    (boundaryJetSecond a.1 a.2.2 a.2.2,a.2.1)) (x := a) (hP.prodMk hn.continuousAt)
  filter_upwards [hd.continuousAt.eventually_ne ha.1,hh.eventually (isOpen_Ioi.mem_nhds ha.2)] with b hb hp
  exact ⟨hb,hp⟩

theorem compact_boundary_jet_positivity {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {J : X → BoundaryProfile} {n : X → Vec} {v : X → Base}
    (hJ : Continuous J) (hn : Continuous n) (hv : Continuous v)
    (hold : ∀ x, (J x,n x,v x) ∈ boundaryJetPositivity) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : X, ∀ H : BoundaryProfile, ∀ m : Vec,
      ‖H-J x‖ < δ → ‖m-n x‖ < δ → 0 < boundaryJetSecond H (v x) (v x) ⬝ᵥ m := by
  let f := fun x => (J x,n x,v x)
  have hf : Continuous f := hJ.prodMk (hn.prodMk hv)
  obtain ⟨δ,hδ,hsub⟩ := (isCompact_range hf).exists_cthickening_subset_open
    isOpen_boundaryJetPositivity (by rintro _ ⟨x,rfl⟩; exact hold x)
  refine ⟨δ,hδ,?_⟩
  intro x H m hH hm
  apply And.right (a := NormalFrame.gramDet (H 0) (H 1) ≠ 0)
  change (H,m,v x) ∈ boundaryJetPositivity
  apply hsub
  apply Metric.thickening_subset_cthickening
  apply Metric.mem_thickening_iff.mpr
  refine ⟨f x,mem_range_self x,?_⟩
  change dist (H,(m,v x)) (J x,(n x,v x)) < δ
  rw [Prod.dist_eq,dist_prod_same_right,dist_eq_norm,dist_eq_norm]
  exact max_lt hH hm

theorem compact_actual_exterior_pairing {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {F : RField 4} (hF : ContDiff ℝ ∞ F) {p : X → Base} {n : X → Vec} {v : X → Base}
    (hp : Continuous p) (hn : Continuous n) (hv : Continuous v)
    (hD : ∀ x, NormalFrame.gramDet (coordDeriv dx F (p x)) (coordDeriv dy F (p x)) ≠ 0)
    (hpositive : ∀ x, 0 < realSecondForm F (v x) (v x) (p x) ⬝ᵥ n x) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : X, ∀ G : RField 4, ContDiff ℝ ∞ G → ∀ m : Vec,
      ‖realBoundaryProfile G 1 (p x)-realBoundaryProfile F 1 (p x)‖ < δ →
      ‖m-n x‖ < δ → 0 < realSecondForm G (v x) (v x) (p x) ⬝ᵥ m := by
  have hJ : Continuous (fun x => realBoundaryProfile F 1 (p x)) :=
    (realBoundaryProfile_smooth hF 1).continuous.comp hp
  obtain ⟨δ,hδ,hclose⟩ := compact_boundary_jet_positivity hJ hn hv (by
    intro x
    refine ⟨hD x,?_⟩
    rw [boundaryJetSecond_actual hF]
    exact hpositive x)
  refine ⟨δ,hδ,?_⟩
  intro x G hG m hnear hm
  simpa only [boundaryJetSecond_actual hG] using hclose x (realBoundaryProfile G 1 (p x)) m hnear hm

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
