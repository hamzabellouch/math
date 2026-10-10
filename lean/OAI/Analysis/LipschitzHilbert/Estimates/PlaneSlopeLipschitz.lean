import OAI.Analysis.LipschitzHilbert.Estimates.PlaneCoordinates
import OAI.Analysis.LipschitzHilbert.Geometry.SlopeDirection

namespace OAI

/-! Transfer the Euclidean-plane Lipschitz field to the product-coordinate
metric used by the geometric witness and line-counting arguments. -/

noncomputable section
open scoped NNReal
namespace LipschitzHilbert

theorem planeCoordinates_lipschitz : LipschitzWith 2 planeCoordinates := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  have h := plane_norm_le_coordinate_sum (planeCoordinates z-planeCoordinates w)
  simp only [planeCoordinates_apply,PiLp.sub_apply,Matrix.cons_val_zero,Matrix.cons_val_one] at h
  rw [dist_eq_norm]
  apply h.trans
  change |z.1-w.1|+|z.2-w.2| ≤ (2:ℝ)*dist z w
  rw [Prod.dist_eq,Real.dist_eq,Real.dist_eq]
  linarith [le_max_left |z.1-w.1| |z.2-w.2|,le_max_right |z.1-w.1| |z.2-w.2|]

theorem product_slope_lipschitz (u : Plane → ℝ) {K : ℝ≥0} (hu : LipschitzWith K u) :
    LipschitzWith (2*K) (fun z : ℝ × ℝ => u (planeCoordinates z)) := by
  simpa only [mul_comm,Function.comp_def] using hu.comp planeCoordinates_lipschitz

end LipschitzHilbert

end

end OAI
