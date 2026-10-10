import OAI.MeasureTheory.Falconer.Geometry.ScalarNormalizedProjection

namespace OAI

/-! The normalization radius has an inverse controlled by the original
 weak Frostman constant, with exactly the reserved exponent. -/
namespace Falconer

 theorem scalar_density_inverse_bound {R κ K : ℝ} (hR : 0 < R) (hκ : 0 < κ)
    (hK : 0 < K) (hbound : 1 ≤ (2:ℝ)^κ*K*R^κ) :
    R⁻¹ ≤ 2*K^(1/κ) := by
  have hpow : (R⁻¹)^κ ≤ (2:ℝ)^κ*K := by
    rw [Real.inv_rpow hR.le,inv_eq_one_div]
    exact (div_le_iff₀ (Real.rpow_pos_of_pos hR κ)).2 (by nlinarith)
  have hh := Real.rpow_le_rpow (by positivity : 0 ≤ (R⁻¹)^κ) hpow
    (by positivity : 0 ≤ 1/κ)
  have hl : ((R⁻¹)^κ)^(1/κ) = R⁻¹ := by
    rw [← Real.rpow_mul (by positivity),mul_one_div_cancel hκ.ne',Real.rpow_one]
  have hr : ((2:ℝ)^κ*K)^(1/κ) = 2*K^(1/κ) := by
    rw [Real.mul_rpow (by positivity) hK.le,← Real.rpow_mul (by positivity),
      mul_one_div_cancel hκ.ne',Real.rpow_one]
  simpa only [hl,hr] using hh

 theorem scalar_density_radius_strict {δ κ K R : ℝ}
    (hδR : δ ≤ R) (hbound : 1 ≤ (2:ℝ)^κ*K*R^κ)
    (hsmall : (2:ℝ)^κ*K*δ^κ < 1) : δ < R := by
  apply lt_of_le_of_ne hδR
  intro he
  rw [he] at hsmall
  linarith

end Falconer

end OAI
