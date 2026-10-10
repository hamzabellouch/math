import OAI.Analysis.LipschitzHilbert.Geometry.FarSelectionGeometry

namespace OAI

/-! Actual distances between points with the same projected coordinate,
used to compare directions within one projected-popularity group. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace LipschitzHilbert.Rectangle

theorem dist_of_same_long_coordinate (S : Rectangle) (x y : Plane)
    (hxy : (S.orthogonalCoordinates x).1 = (S.orthogonalCoordinates y).1) :
    dist x y = |(S.orthogonalCoordinates y).2-(S.orthogonalCoordinates x).2| := by
  have h0 : S.axes.repr (y-x) 0 = 0 := by
    rw [←S.coordinate_difference x y 0]
    change (S.orthogonalCoordinates y).1-(S.orthogonalCoordinates x).1=0
    rw [hxy,sub_self]
  have he : y-x = S.axes.repr (y-x) 1 • S.axes 1 := by
    have h := S.axes.sum_repr (y-x)
    rw [Fin.sum_univ_two,h0,zero_smul,zero_add] at h
    exact h.symm
  rw [dist_eq_norm,norm_sub_rev,he,norm_smul,S.axes.norm_eq_one,mul_one,Real.norm_eq_abs,
    ←S.coordinate_difference x y 1]
  rfl

theorem transverse_position_bound (S R : Rectangle) (x : Plane) (hx : x ∈ R.carrier)
    (hint : (R.carrier ∩ S.carrier).Nonempty) :
    |(S.orthogonalCoordinates x).2| ≤ S.short/2+R.long*dist (S.axes 0) (R.axes 0)+R.short := by
  obtain ⟨y,hyR,hyS⟩ := hint
  have hd := S.transverse_difference_le R hx hyR
  rw [←S.coordinate_difference y x 1] at hd
  have ht := abs_add_le
    (S.axes.repr (x-S.center) 1-S.axes.repr (y-S.center) 1) (S.axes.repr (y-S.center) 1)
  simp only [sub_add_cancel] at ht
  change |S.axes.repr (x-S.center) 1| ≤ _
  linarith [hyS.2]

theorem shared_projection_distance (S R T : Rectangle) (x y : Plane)
    (hx : x ∈ R.carrier) (hy : y ∈ T.carrier)
    (hR : (R.carrier ∩ S.carrier).Nonempty) (hT : (T.carrier ∩ S.carrier).Nonempty)
    (hxy : (S.orthogonalCoordinates x).1 = (S.orthogonalCoordinates y).1) :
    dist x y ≤ S.short+R.long*dist (S.axes 0) (R.axes 0)+R.short+
      T.long*dist (S.axes 0) (T.axes 0)+T.short := by
  rw [S.dist_of_same_long_coordinate x y hxy]
  have h := abs_sub (S.orthogonalCoordinates y).2 (S.orthogonalCoordinates x).2
  have hx' := S.transverse_position_bound R x hx hR
  have hy' := S.transverse_position_bound T y hy hT
  linarith

end LipschitzHilbert.Rectangle

end

end OAI
