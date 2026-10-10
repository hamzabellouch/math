import Mathlib

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct
open scoped TensorProduct InnerProductSpace Topology
open UniformSpace Completion Filter
open scoped TensorProduct
open UniformSpace Completion
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace Kadison

theorem square_endpoint_unit_bound (r C m : ℝ) (p c : ℕ)
    (hr : 0 ≤ r) (hC : 0 ≤ C) (hm : 0 < m) (hp : 1 ≤ p)
    (h : r * (m⁻¹) ^ c ≤ C * m⁻¹ * (Real.sqrt m⁻¹) ^ (p - 1)) :
    r ^ 2 * m ^ (p + 1) ≤ C ^ 2 * m ^ (2 * c) := by
  have hq : 0 ≤ m⁻¹ := inv_nonneg.mpr hm.le
  have hleft : (r * (m⁻¹) ^ c) ^ 2 = r ^ 2 * (m⁻¹) ^ (2 * c) := by
    rw [mul_pow, ← pow_mul, Nat.mul_comm c 2]
  have hright : (C * m⁻¹ * (Real.sqrt m⁻¹) ^ (p - 1)) ^ 2 =
      C ^ 2 * (m⁻¹) ^ (p + 1) := by
    simp only [mul_pow]
    rw [pow_right_comm (Real.sqrt m⁻¹) (p - 1) 2, Real.sq_sqrt hq,
      mul_assoc, ← pow_add, show 2 + (p - 1) = p + 1 by omega]
  have hs := (sq_le_sq₀ (mul_nonneg hr (pow_nonneg hq _))
    (mul_nonneg (mul_nonneg hC hq) (pow_nonneg (Real.sqrt_nonneg _) _))).mpr h
  rw [hleft, hright, inv_pow, inv_pow, ← div_eq_mul_inv, ← div_eq_mul_inv] at hs
  exact (div_le_div_iff₀ (pow_pos hm _) (pow_pos hm _)).mp hs

end Kadison
end

end OAI
