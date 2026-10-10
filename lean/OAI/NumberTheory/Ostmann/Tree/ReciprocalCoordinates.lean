import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic

namespace OAI

/-!
# Reciprocal coordinates for the uniform Mellin estimate

The change of variables `r = lam - 1/d` is a permutation even with
the field's zero-inverse convention. Away from the singular bottom-pair
ratio, it turns reciprocal leaf arguments into a quadratic affine map.
-/

namespace Ostmann

variable {K : Type*} [Field K]

def reciprocalCoordinates (lam : K) : K ≃ K where
  toFun d := lam - d⁻¹
  invFun r := (lam - r)⁻¹
  left_inv d := by simp
  right_inv r := by simp

theorem reciprocal_right_argument (lam d : K) (hd : d ≠ 0) :
    (d / (lam * d - 1))⁻¹ = lam - d⁻¹ := by
  rw [inv_div]
  field_simp

theorem reciprocal_left_argument (lam d : K) (hlam : lam ≠ 0) (hd : d ≠ 0) :
    (d * (lam * d) / (lam * d - 1))⁻¹ =
      (lam - d⁻¹) - (lam - d⁻¹) ^ 2 / lam := by
  rw [inv_div]
  field_simp
  ring

theorem reciprocal_coordinate_eq_zero (lam d : K) (hd : d ≠ 0) :
    lam - d⁻¹ = 0 ↔ lam * d = 1 := by
  rw [sub_eq_zero]
  constructor
  · intro h
    rw [h, inv_mul_cancel₀ hd]
  · intro h
    exact mul_right_cancel₀ hd (by simpa only [inv_mul_cancel₀ hd] using h)

end Ostmann

end OAI
