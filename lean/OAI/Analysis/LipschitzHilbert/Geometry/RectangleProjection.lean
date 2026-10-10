import OAI.Analysis.LipschitzHilbert.Fourier.StripProjection
import OAI.Analysis.LipschitzHilbert.Geometry.FiniteTransverseDirections

namespace OAI

/-! Compact coordinate projections and exact change of orthogonal
coordinates for the popularity packing in Lacey--Li (3.11). -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal BigOperators
namespace LipschitzHilbert.Rectangle

theorem isClosed_carrier (R : Rectangle) : IsClosed R.carrier := by
  change IsClosed ({x : Plane | |R.axes.repr (x-R.center) 0| ≤ R.long/2} ∩
    {x : Plane | |R.axes.repr (x-R.center) 1| ≤ R.short/2})
  exact (isClosed_le (by fun_prop) continuous_const).inter (isClosed_le (by fun_prop) continuous_const)

theorem isCompact_carrier (R : Rectangle) : IsCompact R.carrier := by
  apply Metric.isCompact_of_isClosed_isBounded R.isClosed_carrier
  apply (Metric.isBounded_closedBall (x := R.center) (r := R.long)).subset
  intro x hx
  simpa only [Metric.mem_closedBall,dist_eq_norm] using R.norm_sub_center_le_long hx

theorem isCompact_popularSet (R : Rectangle) {v : Plane → Plane} (hv : Continuous v) :
    IsCompact (R.popularSet v) := by
  change IsCompact (R.carrier ∩ {x | Real.cos (R.short/(2*R.long)) ≤ inner ℝ (v x) (R.axes 0)})
  exact R.isCompact_carrier.inter_right (isClosed_le continuous_const (hv.inner continuous_const))

theorem continuous_orthogonalCoordinates (R : Rectangle) : Continuous R.orthogonalCoordinates := by
  change Continuous (fun x : Plane => (R.axes.repr (x-R.center) 0,R.axes.repr (x-R.center) 1))
  fun_prop

def coordinateProjection (S : Rectangle) (E : Set Plane) : Set ℝ :=
  (fun x => (S.orthogonalCoordinates x).1) '' E

theorem isCompact_coordinateProjection (S : Rectangle) {E : Set Plane} (hE : IsCompact E) :
    IsCompact (S.coordinateProjection E) :=
  hE.image (continuous_fst.comp S.continuous_orthogonalCoordinates)

theorem change_transverse_coordinates (R S : Rectangle) (x : Plane) :
    R.axes.repr (x-R.center) 1 =
      R.axes.repr (S.axes 0) 1 * (S.orthogonalCoordinates x).1 +
      R.axes.repr (S.axes 1) 1 * (S.orthogonalCoordinates x).2 +
      R.axes.repr (S.center-R.center) 1 := by
  have he : x-R.center = (x-S.center)+(S.center-R.center) := by abel
  rw [he,map_add,PiLp.add_apply]
  nth_rw 1 [←S.axes.sum_repr (x-S.center)]
  rw [Fin.sum_univ_two,map_add,PiLp.add_apply,map_smul,map_smul]
  change (S.axes.repr (x-S.center) 0)*R.axes.repr (S.axes 0) 1 +
    (S.axes.repr (x-S.center) 1)*R.axes.repr (S.axes 1) 1 + R.axes.repr (S.center-R.center) 1 = _
  rw [orthogonalCoordinates_apply]
  ring

theorem coordinate_projection_area (R S : Rectangle) {E : Set Plane} (hE : IsCompact E)
    (hsub : E ⊆ R.carrier) (hangle : dist (R.axes 0) (S.axes 0) ≤ 1/4) :
    volume E ≤ ENNReal.ofReal (2*R.short)*volume (S.coordinateProjection E) := by
  let E' := S.orthogonalCoordinates '' E
  have hE' : IsCompact E' := hE.image S.continuous_orthogonalCoordinates
  have hP := S.isCompact_coordinateProjection hE
  have hb : 1/2 ≤ |R.axes.repr (S.axes 1) 1| := by
    have h := nearby_transverse_coordinate S R S.transverseFrame hangle
      (show dist (S.transverseFrame.axes 0) (S.axes 1) ≤ 1/4 by rw [transverseFrame_axis]; norm_num)
    simpa only [transverseFrame_axis] using h
  have h := LipschitzHilbert.strip_projection_area_half E' hE'.measurableSet
    (S.coordinateProjection E) hP.measurableSet
    (R.axes.repr (S.axes 0) 1) (R.axes.repr (S.axes 1) 1)
    (-R.axes.repr (S.center-R.center) 1) (R.short/2) hb (half_pos R.short_pos).le
    (fun z hz => by obtain ⟨x,hx,rfl⟩ := hz; exact ⟨x,hx,rfl⟩)
    (fun z hz => by
      obtain ⟨x,hx,rfl⟩ := hz
      have hh := (hsub hx).2
      rw [change_transverse_coordinates R S x] at hh
      simpa only [sub_neg_eq_add] using hh)
  have he : (volume.prod volume) E' = volume E := by
    have he := S.orthogonalCoordinates_measurePreserving.measure_preimage_equiv E'
    rw [Set.preimage_image_eq E S.orthogonalCoordinates.injective] at he
    exact he.symm
  rw [he] at h
  have hc : 4*(R.short/2) = 2*R.short := by ring
  rw [hc] at h
  exact h

theorem popular_projection_density (R S : Rectangle) {v : Plane → Plane} {K δ : ℝ≥0}
    (hv : Continuous v) (hR : R.Admissible v K δ)
    (hangle : dist (R.axes 0) (S.axes 0) ≤ 1/4) :
    (δ : ℝ≥0∞)*ENNReal.ofReal R.long ≤ 2*volume (S.coordinateProjection (R.popularSet v)) := by
  have hp := coordinate_projection_area R S (R.isCompact_popularSet hv)
    (fun _ hx => hx.1) hangle
  have hm := hR.2.trans hp
  rw [volume_carrier] at hm
  have hh : ENNReal.ofReal R.short * ((δ : ℝ≥0∞)*ENNReal.ofReal R.long) ≤
      ENNReal.ofReal R.short * (2*volume (S.coordinateProjection (R.popularSet v))) := by
    calc
      _ = (δ : ℝ≥0∞)*(ENNReal.ofReal R.long*ENNReal.ofReal R.short) := by ring
      _ ≤ ENNReal.ofReal (2*R.short)*volume (S.coordinateProjection (R.popularSet v)) := hm
      _ = _ := by rw [ENNReal.ofReal_mul (by norm_num)]; norm_num; ring
  exact (ENNReal.mul_le_mul_iff_right (ne_of_gt (ENNReal.ofReal_pos.mpr R.short_pos))
    ENNReal.ofReal_ne_top).mp hh

theorem projection_in_long_interval (R S : Rectangle) (hL : R.long ≤ S.long)
    (hint : (R.carrier ∩ S.carrier).Nonempty) {E : Set Plane} (hE : E ⊆ R.carrier) :
    S.coordinateProjection E ⊆ Icc (-3*S.long) (3*S.long) := by
  obtain ⟨y,hyR,hyS⟩ := hint
  rintro u ⟨x,hx,rfl⟩
  have hn : ‖x-S.center‖ ≤ 3*S.long := by
    have hdist := R.dist_le_two_long (hE hx) hyR
    rw [dist_eq_norm] at hdist
    have htri : ‖x-S.center‖ ≤ ‖x-y‖+‖y-S.center‖ := by
      simpa only [dist_eq_norm] using dist_triangle x y S.center
    linarith [S.norm_sub_center_le_long hyS]
  have hc := (S.abs_coordinate_le_norm (x-S.center) 0).trans hn
  simpa only [orthogonalCoordinates_apply,mem_Icc,neg_mul] using abs_le.mp hc

end LipschitzHilbert.Rectangle

end

end OAI
