import OAI.Geometry.SurfaceImmersion.Geometry.BoundaryJetPositivity
import OAI.Geometry.SurfaceImmersion.Primitive.CrossingPositivePairing

namespace OAI

/-! Uniform strict data for the interior/exterior normal interpolation.
The new canonical yy normal and the exterior normal both pair positively
with every later curve meeting the support boundary. -/
noncomputable section
open Set Filter
open scoped ContDiff Matrix Topology
namespace ClosedSurfaceR4.GeometryPreservation
open SmallModes RealModes NormalFrame VelocityFrame

def boundaryPreferredPairing : Set (BoundaryProfile × Base) :=
  {a | a.1 ∈ regularBoundaryProfiles ∧ 0 < boundaryJetSecond a.1 a.2 a.2 ⬝ᵥ profilePreferred a.1}

lemma isOpen_boundaryPreferredPairing : IsOpen boundaryPreferredPairing := by
  apply isOpen_iff_mem_nhds.mpr
  intro a ha
  have hr : ContinuousAt (fun b : BoundaryProfile × Base => b.1) a := continuous_fst.continuousAt
  have hp := (continuousAt_boundaryJetSecond a.2 a.2 ha.1.1).comp
    (f := fun b : BoundaryProfile × Base => (b.1,b.2,b.2)) (x := a)
    (by fun_prop : ContinuousAt (fun b : BoundaryProfile × Base => (b.1,b.2,b.2)) a)
  have hn := (contDiffAt_profilePreferred ha.1).continuousAt.comp hr
  have hdot : Continuous (fun p : Vec × Vec => p.1 ⬝ᵥ p.2) := by
    unfold dotProduct
    fun_prop
  have hh := hdot.continuousAt.comp (f := fun b : BoundaryProfile × Base =>
    (boundaryJetSecond b.1 b.2 b.2,profilePreferred b.1)) (x := a) (hp.prodMk hn)
  exact (hr.eventually (isOpen_regularBoundaryProfiles.mem_nhds ha.1)).and
    (hh.eventually (isOpen_Ioi.mem_nhds ha.2))

lemma profilePreferred_real (F : RField 4) (z : ℝ) (p : Base) :
    profilePreferred (realBoundaryProfile F z p) = normalize (realSecondForm F dy dy p) := rfl

lemma compact_actual_preferred_pairing {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {F : RField 4} (hF : ContDiff ℝ ∞ F) {p : X → Base} {v : X → Base}
    (hp : Continuous p) (hv : Continuous v)
    (hD : ∀ x, NormalFrame.gramDet (coordDeriv dx F (p x)) (coordDeriv dy F (p x)) ≠ 0)
    (hB : ∀ x, realSecondForm F dy dy (p x) ≠ 0)
    (hpos : ∀ x, 0 < realSecondForm F (v x) (v x) (p x) ⬝ᵥ normalize (realSecondForm F dy dy (p x))) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : X, ∀ G : RField 4, ContDiff ℝ ∞ G →
      ‖realBoundaryProfile G 1 (p x)-realBoundaryProfile F 1 (p x)‖ < δ →
      ∀ z : ℝ, 0 < realSecondForm G (v x) (v x) (p x) ⬝ᵥ profilePreferred (realBoundaryProfile G z (p x)) := by
  let f := fun x => (realBoundaryProfile F 1 (p x),v x)
  have hf : Continuous f := ((realBoundaryProfile_smooth hF 1).continuous.comp hp).prodMk hv
  have hmem (x : X) : f x ∈ boundaryPreferredPairing := by
    refine ⟨realBoundaryProfile_regular 1 (hD x) (hB x),?_⟩
    simpa only [f,boundaryJetSecond_actual hF,profilePreferred_real] using hpos x
  obtain ⟨δ,hδ,hsub⟩ := (isCompact_range hf).exists_cthickening_subset_open
    isOpen_boundaryPreferredPairing (by rintro _ ⟨x,rfl⟩; exact hmem x)
  refine ⟨δ,hδ,?_⟩
  intro x G hG hclose z
  have hm : (realBoundaryProfile G 1 (p x),v x) ∈ boundaryPreferredPairing := by
    apply hsub
    apply Metric.thickening_subset_cthickening
    apply Metric.mem_thickening_iff.mpr
    refine ⟨f x,mem_range_self x,?_⟩
    change dist (realBoundaryProfile G 1 (p x),v x) (realBoundaryProfile F 1 (p x),v x) < δ
    rwa [dist_prod_same_right,dist_eq_norm]
  simpa only [boundaryJetSecond_actual hG,profilePreferred_real] using hm.2

theorem compact_actual_boundary_matching {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {F : RField 4} (hF : ContDiff ℝ ∞ F) {p : X → Base} {v : X → Base} {n : X → Vec}
    (hp : Continuous p) (hv : Continuous v) (hn : Continuous n)
    (hD : ∀ x, NormalFrame.gramDet (coordDeriv dx F (p x)) (coordDeriv dy F (p x)) ≠ 0)
    (hB : ∀ x, realSecondForm F dy dy (p x) ≠ 0)
    (havoid : ∀ x, n x ≠ -normalize (realSecondForm F dy dy (p x)))
    (hpos : ∀ x, 0 < realSecondForm F (v x) (v x) (p x) ⬝ᵥ n x)
    (κ : X → ℝ)
    (hGauss : ∀ x, coordinateGauss (realMetric F dx dx) (realMetric F dx dy)
      (realMetric F dy dy) (p x) = κ x * NormalFrame.gramDet (coordDeriv dx F (p x)) (coordDeriv dy F (p x)))
    (hQ : ∀ x, 0 < orderedCrossing F dy (v x) (p x) (κ x)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : X, ∀ G : RField 4, ContDiff ℝ ∞ G → ∀ m : Vec,
      ‖realBoundaryProfile G 1 (p x)-realBoundaryProfile F 1 (p x)‖ < δ →
      ‖m-n x‖ < δ → ∀ z : ℝ,
      realSecondForm G dy dy (p x) ≠ 0 ∧
      m ≠ -profilePreferred (realBoundaryProfile G z (p x)) ∧
      0 < realSecondForm G (v x) (v x) (p x) ⬝ᵥ m ∧
      0 < realSecondForm G (v x) (v x) (p x) ⬝ᵥ profilePreferred (realBoundaryProfile G z (p x)) := by
  obtain ⟨δa,hδa,ha⟩ := compact_actual_exterior_avoidance hF hp hn continuous_const hD hB havoid
  obtain ⟨δp,hδp,hpair⟩ := compact_actual_exterior_pairing hF hp hn hv hD hpos
  obtain ⟨δn,hδn,hpref⟩ := compact_actual_preferred_pairing hF hp hv hD hB
    (fun x => orderedCrossing_pos_pure_pairing hF (p x) dy (v x) (κ x) (hD x) (hB x) (hGauss x) (hQ x))
  let δ := min δa (min δp δn)
  have hδa' : δ ≤ δa := min_le_left _ _
  have hδp' : δ ≤ δp := (min_le_right _ _).trans (min_le_left _ _)
  have hδn' : δ ≤ δn := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨δ,lt_min hδa (lt_min hδp hδn),?_⟩
  intro x G hG m hGclose hm z
  obtain ⟨hB',hanti⟩ := ha x G hG m (hGclose.trans_le hδa') (hm.trans_le hδa')
  exact ⟨hB',by simpa only [profilePreferred_real] using hanti,
    hpair x G hG m (hGclose.trans_le hδp') (hm.trans_le hδp'),
    hpref x G hG (hGclose.trans_le hδn') z⟩

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
