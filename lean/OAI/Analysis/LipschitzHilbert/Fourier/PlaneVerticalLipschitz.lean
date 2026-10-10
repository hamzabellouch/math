import OAI.Analysis.LipschitzHilbert.Estimates.PlaneSlopeLipschitz

namespace OAI

/-! The vertical Euclidean coordinate has Lipschitz constant exactly one. -/
noncomputable section
namespace LipschitzHilbert

theorem planeCoordinates_vertical_dist (x y z : ℝ) :
    dist (planeCoordinates (x,y)) (planeCoordinates (x,z))=dist y z := by
  have hs : dist (planeCoordinates (x,y)) (planeCoordinates (x,z))^2=dist y z^2 := by
    rw [dist_eq_norm,EuclideanSpace.norm_sq_eq]
    simp only [Fin.sum_univ_two,planeCoordinates_apply,PiLp.sub_apply,
      Matrix.cons_val_zero,Matrix.cons_val_one,sub_self,abs_zero,zero_pow (by decide : 2≠0),
      zero_add,Real.dist_eq,Real.norm_eq_abs]
  exact (sq_eq_sq₀ dist_nonneg dist_nonneg).mp hs

theorem product_slope_vertical_lipschitz (u : Plane → ℝ) (hu : LipschitzWith 1 u) (x : ℝ) :
    LipschitzWith 1 (fun y => u (planeCoordinates (x,y))) := by
  apply LipschitzWith.of_dist_le_mul
  intro y z
  simpa only [NNReal.coe_one,one_mul,planeCoordinates_vertical_dist] using
    hu.dist_le_mul (planeCoordinates (x,y)) (planeCoordinates (x,z))

end LipschitzHilbert

end

end OAI
