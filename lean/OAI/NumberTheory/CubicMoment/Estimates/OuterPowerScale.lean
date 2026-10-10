import OAI.NumberTheory.CubicMoment.Estimates.OuterScale

namespace OAI

/-! Restore the primal powers after summing at the dual Poisson scale. -/
noncomputable section
namespace CubicFirstMoment

lemma outer_poisson_power_scale {Z N R : ℝ} (hZ : 0 < Z) (hN : 0 < N)
    (hR : 0 < R) (ε α β : ℝ) :
    (Z/N)*(4*R*N)^ε*(R*N)^β*(Z/(27*N^2))^(-α) =
      (4*R)^ε*R^β*27^α*Z^(1-α)*N^(ε+β+2*α-1) := by
  have ht : (Z/(27*N^2))^(-α) = 27^α*N^(2*α)/Z^α := by
    rw [Real.rpow_neg (by positivity : 0 ≤ Z/(27*N^2)),
      Real.div_rpow hZ.le (by positivity : 0 ≤ 27*N^2),
      Real.mul_rpow (by norm_num : (0:ℝ) ≤ 27) (sq_nonneg N),inv_div,
      ← Real.rpow_natCast N 2,← Real.rpow_mul hN.le]
    norm_num
  have hz : Z^(1-α) = Z/Z^α := by rw [Real.rpow_sub hZ,Real.rpow_one]
  have hn : N^(ε+β+2*α-1) = N^ε*N^β*N^(2*α)/N := by
    rw [Real.rpow_sub hN,Real.rpow_add hN,Real.rpow_add hN,Real.rpow_one]
  rw [ht,hz,hn,Real.mul_rpow (by positivity : 0 ≤ 4*R) hN.le,
    Real.mul_rpow hR.le hN.le]
  ring

end CubicFirstMoment

end

end OAI
