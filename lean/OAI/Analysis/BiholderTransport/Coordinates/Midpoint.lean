import Mathlib

namespace OAI

section
section
noncomputable section
open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

namespace WeakMTWTransport
open Matrix
open scoped MatrixOrder

lemma power_reduction_exponent {beta : ℝ} (hb : 0 < beta) :
    0 < min beta 1 / 2 ∧ min beta 1 / 2 ≤ 1 := by
  constructor
  · exact div_pos (lt_min hb (by norm_num)) (by norm_num)
  · have := min_le_right beta (1 : ℝ)
    linarith

lemma scalar_power_small {r beta C0 F : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hC : 0 ≤ C0) (hF : F ≤ C0 * r ^ beta) :
    F + r ≤ (C0 + 1) * r ^ (min beta 1) := by
  have hpow := Real.rpow_le_rpow_of_exponent_ge hr hr1 (min_le_left beta 1)
  have hlin : r ≤ r ^ min beta 1 := by
    simpa using Real.rpow_le_rpow_of_exponent_ge hr hr1 (min_le_right beta 1)
  nlinarith [mul_le_mul_of_nonneg_left hpow hC]

lemma scalar_sqrt_power_bound {r beta C0 F : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hC : 0 ≤ C0) (hF : F ≤ C0 * r ^ beta) :
    Real.sqrt (8 * (F + r)) ≤
      Real.sqrt (8 * (C0 + 1)) * r ^ (min beta 1 / 2) := by
  have hsmall := scalar_power_small hr hr1 hC hF
  have h := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hsmall (by norm_num : (0 : ℝ) ≤ 8))
  rw [← mul_assoc, Real.sqrt_mul (by positivity : 0 ≤ 8 * (C0 + 1))] at h
  have heq : Real.sqrt (r ^ min beta 1) = r ^ (min beta 1 / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hr.le]
    congr 1
    ring
  rwa [heq] at h

end WeakMTWTransport
end
end
end

end OAI
