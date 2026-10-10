import Mathlib

namespace OAI


namespace Problem355.PlaneDeterminant

open Matrix
open scoped Matrix

variable {R : Type*} [CommRing R]

theorem normal_smul_cross (y u v w : Fin 3 → R)
    (hv : y ⬝ᵥ v = 0) (hw : y ⬝ᵥ w = 0) :
    (y ⬝ᵥ u) • (v ⨯₃ w) = (Matrix.det ![u, v, w]) • y := by
  have hc : y ⨯₃ (v ⨯₃ w) = 0 := by
    rw [cross_cross_eq_smul_sub_smul', hw, dotProduct_comm v y, hv]
    simp
  have h := cross_cross_eq_smul_sub_smul' u y (v ⨯₃ w)
  rw [hc] at h
  symm
  simpa only [map_zero, triple_product_eq_det, sub_eq_zero] using h.symm

theorem abs_dot_mul_norm_cross (y u v w : Fin 3 → ℝ)
    (hv : y ⬝ᵥ v = 0) (hw : y ⬝ᵥ w = 0) :
    |y ⬝ᵥ u| * ‖WithLp.toLp 2 (v ⨯₃ w)‖ =
      |Matrix.det ![u, v, w]| * ‖WithLp.toLp 2 y‖ := by
  have h := congrArg (fun z : Fin 3 → ℝ => ‖WithLp.toLp 2 z‖)
    (normal_smul_cross y u v w hv hw)
  simpa only [WithLp.toLp_smul, norm_smul, Real.norm_eq_abs] using h

theorem norm_cross_eq_det_mul_norm_div (y u v w : Fin 3 → ℝ)
    (hv : y ⬝ᵥ v = 0) (hw : y ⬝ᵥ w = 0) (hu : y ⬝ᵥ u ≠ 0) :
    ‖WithLp.toLp 2 (v ⨯₃ w)‖ =
      |Matrix.det ![u, v, w]| * ‖WithLp.toLp 2 y‖ / |y ⬝ᵥ u| := by
  apply (eq_div_iff (abs_ne_zero.mpr hu)).mpr
  simpa only [mul_comm] using abs_dot_mul_norm_cross y u v w hv hw

end Problem355.PlaneDeterminant

end OAI
