import OAI.Analysis.LipschitzHilbert.Geometry.FatRectangleSum
import OAI.Analysis.LipschitzHilbert.Geometry.RectangleProjection

namespace OAI

/-! A quantitative interior neighborhood of a dilated rectangle. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace LipschitzHilbert
open DyadicLineGrid

theorem plane_norm_le_coordinate_sum (z : Plane) : ‖z‖ ≤ |z 0|+|z 1| := by
  let b : OrthonormalBasis (Fin 2) ℝ Plane := EuclideanSpace.basisFun (Fin 2) ℝ
  calc
    ‖z‖ = ‖∑ i : Fin 2, b.repr z i • b i‖ := by rw [b.sum_repr]
    _ ≤ ∑ i : Fin 2, ‖b.repr z i • b i‖ := norm_sum_le _ _
    _ = _ := by simp only [Fin.sum_univ_two,norm_smul,b.norm_eq_one,mul_one,Real.norm_eq_abs]; rfl

theorem centeredSquare_norm_bound (x : Plane) (r : ℝ) {z : ℝ × ℝ}
    (hz : z ∈ centeredSquare (planeCoordinates.symm x) r) : ‖planeCoordinates z-x‖ ≤ 2*r := by
  have h0 : |z.1-(planeCoordinates.symm x).1| ≤ r := by
    apply abs_le.mpr
    constructor <;> linarith [hz.1.1,hz.1.2]
  have h1 : |z.2-(planeCoordinates.symm x).2| ≤ r := by
    apply abs_le.mpr
    constructor <;> linarith [hz.2.1,hz.2.2]
  have hh := plane_norm_le_coordinate_sum (planeCoordinates z-x)
  change ‖planeCoordinates z-x‖ ≤ |z.1-(planeCoordinates.symm x).1|+|z.2-(planeCoordinates.symm x).2| at hh
  linarith

namespace Rectangle

theorem dilate_interior_ball (R : Rectangle) (a : ℝ) (ha : 0 < a) {x y : Plane}
    (hx : x ∈ (R.dilate (a/2) (half_pos ha)).carrier)
    (hy : ‖y-x‖ ≤ a*R.short/4) : y ∈ (R.dilate a ha).carrier := by
  have hdiff (i : Fin 2) : |R.axes.repr (y-R.center) i-R.axes.repr (x-R.center) i| ≤ a*R.short/4 := by
    rw [R.coordinate_difference]
    exact (R.abs_coordinate_le_norm (y-x) i).trans hy
  have hab (i : Fin 2) : |R.axes.repr (y-R.center) i| ≤
      |R.axes.repr (y-R.center) i-R.axes.repr (x-R.center) i|+|R.axes.repr (x-R.center) i| := by
    simpa only [sub_add_cancel] using abs_add_le
      (R.axes.repr (y-R.center) i-R.axes.repr (x-R.center) i) (R.axes.repr (x-R.center) i)
  change |R.axes.repr (y-R.center) 0| ≤ a*R.long/2 ∧ |R.axes.repr (y-R.center) 1| ≤ a*R.short/2
  change |R.axes.repr (x-R.center) 0| ≤ (a/2)*R.long/2 ∧
    |R.axes.repr (x-R.center) 1| ≤ (a/2)*R.short/2 at hx
  constructor
  · have hwidth := mul_le_mul_of_nonneg_left R.short_le_long ha.le
    linarith [hdiff 0,hab 0]
  · linarith [hdiff 1,hab 1]

theorem dilate_interior_square (R : Rectangle) (a : ℝ) (ha : 0 < a) {x : Plane}
    (hx : x ∈ (R.dilate (a/2) (half_pos ha)).carrier) :
    centeredSquare (planeCoordinates.symm x) (a*R.short/8) ⊆ planeCoordinates ⁻¹' (R.dilate a ha).carrier := by
  intro z hz
  apply R.dilate_interior_ball a ha hx
  have h := centeredSquare_norm_bound x (a*R.short/8) hz
  linarith

end Rectangle
end LipschitzHilbert

end

end OAI
