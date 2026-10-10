import OAI.Analysis.LipschitzHilbert.Geometry.PopularGroupDirections
import OAI.Analysis.LipschitzHilbert.Geometry.ProjectionGroupSelection
import OAI.Analysis.LipschitzHilbert.Geometry.FarSelectionGeometry
import Mathlib.Data.Finset.Pairwise

namespace OAI

/-! Actual finite groups from intersecting popularity projections.  Their
representatives have the packing bound, and every group lies in a long
interval of the size of its representative. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal BigOperators
namespace LipschitzHilbert

namespace Rectangle

theorem projected_popularity_directions (S R T : Rectangle) {v : Plane → Plane} {K : ℝ≥0}
    (hv : LipschitzWith K v) (hu : ∀ x, ‖v x‖ = 1)
    (hscale : 100*(K:ℝ)*S.long ≤ 1) (hRS : R.long ≤ S.long) (hTR : T.long ≤ R.long)
    (hR : (R.carrier ∩ S.carrier).Nonempty) (hT : (T.carrier ∩ S.carrier).Nonempty)
    (hRw : 64*R.short ≤ R.long*dist (S.axes 0) (R.axes 0))
    (hTw : 64*T.short ≤ T.long*dist (S.axes 0) (T.axes 0))
    (hSw : 32*S.short ≤ S.long*dist (S.axes 0) (R.axes 0))
    (hproj : (S.coordinateProjection (R.popularSet v) ∩
      S.coordinateProjection (T.popularSet v)).Nonempty) :
    dist (R.axes 0) (T.axes 0) ≤ dist (S.axes 0) (R.axes 0)/2 := by
  obtain ⟨t,htR,htT⟩ := hproj
  obtain ⟨x,hx,hxt⟩ := htR
  obtain ⟨y,hy,hyt⟩ := htT
  exact popular_group_directions S R T hv hu hscale hRS hTR hR hT hRw hTw hSw
    hx hy (hxt.trans hyt.symm)

theorem projected_group_localization (S R T : Rectangle) {v : Plane → Plane}
    (hTR : T.long ≤ R.long)
    (hproj : (S.coordinateProjection (R.popularSet v) ∩
      S.coordinateProjection (T.popularSet v)).Nonempty) {y : Plane} (hy : y ∈ T.carrier) :
    |(S.orthogonalCoordinates y).1 - (S.orthogonalCoordinates R.center).1| ≤ 3*R.long := by
  obtain ⟨t,htR,htT⟩ := hproj
  obtain ⟨x,hx,hxt⟩ := htR
  obtain ⟨z,hz,hzt⟩ := htT
  have hxR := R.norm_sub_center_le_long hx.1
  have hyz := T.dist_le_two_long hy hz.1
  have hcx : |(S.orthogonalCoordinates x).1-(S.orthogonalCoordinates R.center).1| ≤ R.long := by
    change |S.axes.repr (x-S.center) 0-S.axes.repr (R.center-S.center) 0| ≤ R.long
    rw [coordinate_difference]
    exact (S.abs_coordinate_le_norm (x-R.center) 0).trans hxR
  have hcy : |(S.orthogonalCoordinates y).1-(S.orthogonalCoordinates z).1| ≤ 2*T.long := by
    change |S.axes.repr (y-S.center) 0-S.axes.repr (z-S.center) 0| ≤ 2*T.long
    rw [coordinate_difference]
    exact (S.abs_coordinate_le_norm (y-z) 0).trans (by simpa only [dist_eq_norm] using hyz)
  have hzx : (S.orthogonalCoordinates z).1 = (S.orthogonalCoordinates x).1 := hzt.trans hxt.symm
  rw [hzx] at hcy
  exact (abs_sub_le _ _ _).trans (by linarith)

end Rectangle

/-- The representatives are selected by maximal length. No geometric
packing hypothesis is assumed: their projected popularity sets are disjoint
by construction. -/
theorem exists_projected_popularity_groups {ι : Type*} [DecidableEq ι]
    (R : ι → Rectangle) (s : Finset ι) (S : Rectangle)
    {v : Plane → Plane} {K δ : ℝ≥0} (hv : Continuous v) (hδ : 0 < δ)
    (hR : ∀ j ∈ s, (R j).Admissible v K δ)
    (hL : ∀ j ∈ s, (R j).long ≤ S.long)
    (hinter : ∀ j ∈ s, ((R j).carrier ∩ S.carrier).Nonempty)
    (hangle : ∀ j ∈ s, dist ((R j).axes 0) (S.axes 0) ≤ 1/4) :
    ∃ centers : Finset ι, centers ⊆ s ∧
      (δ : ℝ≥0∞)*(∑ i ∈ centers, ENNReal.ofReal (R i).long) ≤ 12*ENNReal.ofReal S.long ∧
      ∀ j ∈ s, ∃ i ∈ centers, (R j).long ≤ (R i).long ∧
        (S.coordinateProjection ((R i).popularSet v) ∩
          S.coordinateProjection ((R j).popularSet v)).Nonempty := by
  let P := fun j => S.coordinateProjection ((R j).popularSet v)
  obtain ⟨l,hl⟩ := projection_group_run_exists R P s
  have hsub : l.toFinset ⊆ s := by
    intro j hj
    exact hl.selected_subset j (List.mem_toFinset.mp hj)
  have hdisj : (l.toFinset : Set ι).PairwiseDisjoint P :=
    (List.pairwiseDisjoint_iff_coe_toFinset_pairwise_disjoint hl.selected_nodup).mpr
      hl.projected_centers_disjoint
  refine ⟨l.toFinset,hsub,?_,?_⟩
  · exact projected_popularity_packing R l.toFinset S hv
      (fun i hi => hR i (hsub hi)) (fun i hi => hL i (hsub hi))
      (fun i hi => hinter i (hsub hi)) (fun i hi => hangle i (hsub hi)) hdisj
  · intro j hj
    have hn (k : ι) (hk : k ∈ s) : (P k).Nonempty := by
      obtain ⟨x,hx⟩ := (R k).popularSet_nonempty (hR k hk) hδ
      exact ⟨(S.orthogonalCoordinates x).1,x,hx,rfl⟩
    obtain ⟨i,hi,hij,hp⟩ := hl.projected_center_cover (by simp [projectionBlocked]) hn j hj
    exact ⟨i,List.mem_toFinset.mpr hi,hij,hp⟩

end LipschitzHilbert

end

end OAI
