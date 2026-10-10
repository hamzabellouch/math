import OAI.Geometry.CylinderCovering.Angular.Construction
import OAI.Geometry.CylinderCovering.Angular.SharpArea

namespace OAI

noncomputable section
open Set
namespace TriangularCovering.AngularZeroTiltSource

def lower : TriCylinder :=
  lowerCylinder (a := -1) (b := 1) (T := 1 / 2)
    (by norm_num) (by norm_num) 0 0 0

def upper : TriCylinder :=
  upperCylinder (a := -1) (b := 1) (T := 1 / 2)
    (by norm_num) (by norm_num) 0 0 0

def family : Fin 2 → TriCylinder := ![lower, upper]

theorem lower_axis : lower.axis = tiltV 0 0 0 := by
  change unit (tiltV 0 0 0) = _
  simp [unit, tiltV_norm]

theorem upper_axis : upper.axis = tiltW 0 0 0 := by
  change unit (tiltW 0 0 0) = _
  simp [unit, tiltW_norm]

theorem lower_carrier : lower.carrier =
    {z | ∃ p ∈ lowerIntercept (-1) 1 (1 / 2), ∃ r : ℝ,
      z = p + r • tiltV 0 0 0} :=
  lowerCylinder_carrier_intercept (by norm_num) (by norm_num) 0 0 0

theorem upper_carrier : upper.carrier =
    {z | ∃ p ∈ upperIntercept (-1) 1 (1 / 2), ∃ r : ℝ,
      z = p + r • tiltW 0 0 0} :=
  upperCylinder_carrier_intercept (by norm_num) (by norm_num) 0 0 0

theorem covers : Covers family := by
  rintro z ⟨x, y, t, ht0, ht1, hx, hy, rfl⟩
  by_cases ht : t ≤ 1 / 2
  · refine ⟨0, ?_⟩
    change point x y t ∈ lower.carrier
    apply lowerCylinder_hit (by norm_num) (by norm_num) 0 0 0
    all_goals simp only [zero_mul, sub_zero, neg_one_mul]
    · exact ht0
    · exact ht
    · exact (abs_le.mp hy).1
    · simpa using (abs_le.mp hy).2
  · refine ⟨1, ?_⟩
    change point x y t ∈ upper.carrier
    apply upperCylinder_hit (by norm_num) (by norm_num) 0 0 0
    all_goals simp only [zero_mul, add_zero, neg_one_mul]
    · linarith
    · linarith
    · exact (abs_le.mp hx).1
    · simpa using (abs_le.mp hx).2

theorem lower_area : area lower.base = H / 4 := by
  rw [lower, lowerCylinder_area]
  norm_num
  ring

theorem upper_area : area upper.base = H / 4 := by
  rw [upper, upperCylinder_area]
  norm_num
  ring

theorem total_area : totalArea family = A_min / 2 := by
  simp only [totalArea, Fin.sum_univ_two, family, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, lower_area, upper_area]
  rw [projection_minimum]
  ring

theorem relative_cost : relativeCost family = 1 / 2 := by
  have hy : shadowArea (tiltW 0 0 0) = H := by
    rw [shadowArea_formula (by rw [tiltW_norm]; norm_num)]
    simp [tiltW, H_pos.le]
  simp only [relativeCost, Fin.sum_univ_two, family, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, lower_area, upper_area,
    lower_axis, upper_axis, xAxis_shadow, hy]
  field_simp [H_ne_zero]
  ring

end TriangularCovering.AngularZeroTiltSource

end

end OAI
