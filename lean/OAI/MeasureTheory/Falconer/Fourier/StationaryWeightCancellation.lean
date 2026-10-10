import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Ring

namespace OAI

/-! # Exact cancellation of the original distance weight

The fixed weight `q^(-(d-1)/2)` cancels the base spatial power in the
inverse expansion. Only the integer inverse powers need spatial Fourier
separation. The same weight occurs in each direct factor.
-/

namespace Falconer

theorem stationary_weighted_inverse_power (n j : ℕ) {r q : ℝ}
    (hr : 0 < r) (hq : 0 < q) :
    q^(-((n : ℝ)/2))*(r*q)^((n : ℝ)/2)*(r*q)^(-(j : ℝ)) =
      r^((n : ℝ)/2)*(r^j)⁻¹*(q^j)⁻¹ := by
  rw [Real.mul_rpow hr.le hq.le,Real.rpow_neg_natCast,zpow_neg,zpow_natCast,
    mul_pow,mul_inv_rev]
  have hbase : q^(-((n : ℝ)/2))*q^((n : ℝ)/2) = 1 := by
    rw [← Real.rpow_add hq,neg_add_cancel,Real.rpow_zero]
  calc
    _ = (q^(-((n : ℝ)/2))*q^((n : ℝ)/2))*r^((n : ℝ)/2)*(r^j)⁻¹*(q^j)⁻¹ := by ring
    _ = _ := by rw [hbase,one_mul]

theorem stationary_direct_power (n j : ℕ) {r q : ℝ} (hr : 0 < r) (hq : 0 < q) :
    (r*q)^(-((n : ℝ)/2)-(j : ℝ)) =
      r^(-((n : ℝ)/2))*(r^j)⁻¹*q^(-((n : ℝ)/2))*(q^j)⁻¹ := by
  rw [sub_eq_add_neg,Real.rpow_add (mul_pos hr hq),Real.mul_rpow hr.le hq.le,
    Real.rpow_neg_natCast,zpow_neg,zpow_natCast,mul_pow,mul_inv_rev]
  ring

theorem stationary_direct_pair_power (n j k : ℕ) {r q₀ q₁ : ℝ}
    (hr : 0 < r) (hq₀ : 0 < q₀) (hq₁ : 0 < q₁) :
    r^(n : ℝ)*(r*q₀)^(-((n : ℝ)/2)-(j : ℝ))*(r*q₁)^(-((n : ℝ)/2)-(k : ℝ)) =
      (r^(j+k))⁻¹*(q₀^(-((n : ℝ)/2))*q₁^(-((n : ℝ)/2)))*(q₀^j)⁻¹*(q₁^k)⁻¹ := by
  rw [stationary_direct_power n j hr hq₀,stationary_direct_power n k hr hq₁]
  have hbase : r^(n : ℝ)*r^(-((n : ℝ)/2))*r^(-((n : ℝ)/2)) = 1 := by
    rw [← Real.rpow_add hr,← Real.rpow_add hr,
      show (n : ℝ)+-((n : ℝ)/2)+-((n : ℝ)/2) = 0 by ring,Real.rpow_zero]
  calc
    _ = (r^(n : ℝ)*r^(-((n : ℝ)/2))*r^(-((n : ℝ)/2)))*
        ((r^j)⁻¹*(r^k)⁻¹)*(q₀^(-((n : ℝ)/2))*q₁^(-((n : ℝ)/2)))*(q₀^j)⁻¹*(q₁^k)⁻¹ := by ring
    _ = _ := by rw [hbase,one_mul,pow_add,mul_inv_rev]; ring

end Falconer

end OAI
