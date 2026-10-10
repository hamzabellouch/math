import OAI.Geometry.RCD.Coordinates.OutwardCovectorGrowth
import OAI.Geometry.RCD.Coordinates.DyadicRadialFits

namespace OAI

/-! # Vanishing of affine center values at shrinking radial scales -/

open Filter
open scoped Topology

noncomputable section
namespace RegularPointCoordinates

/-- The actual dyadic radius decays faster than the proved covector
growth. Thus the size estimate for affine fit centers forces a zero limit. -/
theorem dyadic_affine_center_tendsto_zero {n : ℕ} {r0 M : ℝ}
    (hr0 : 0 ≤ r0) (hM : 0 ≤ M)
    (F : ℕ → Euclidean n ≃L[ℝ] Euclidean n) (b : Euclidean n)
    (hgrowth : ∀ i, ‖(F i).symm b‖ ≤ (9 / 8 : ℝ) ^ i * ‖(F 0).symm b‖)
    (c : ℕ → ℝ)
    (hsize : ∀ i, |c i| ≤ M * (distanceSourceRadius r0 i / 64) * ‖(F i).symm b‖) :
    Tendsto c atTop (𝓝 0) := by
  have hrad (i : ℕ) : (distanceSourceRadius r0 i / 64) * (9 / 8 : ℝ) ^ i =
      (r0 / 128) * (9 / 16 : ℝ) ^ i := by
    calc
      _ = (r0 / 128) * ((9 / 8 : ℝ) ^ i / (2 : ℝ) ^ i) := by
        unfold distanceSourceRadius
        rw [pow_succ]
        field_simp
        ring
      _ = _ := by rw [← div_pow]; norm_num
  have hbound (i : ℕ) : ‖c i‖ ≤
      (M * (r0 / 128) * ‖(F 0).symm b‖) * (9 / 16 : ℝ) ^ i := by
    rw [Real.norm_eq_abs]
    have hh := mul_le_mul_of_nonneg_left (hgrowth i)
      (show 0 ≤ M * (distanceSourceRadius r0 i / 64) by
        unfold distanceSourceRadius
        positivity)
    apply (hsize i).trans (hh.trans_eq ?_)
    calc
      _ = M * ((distanceSourceRadius r0 i / 64) * (9 / 8 : ℝ) ^ i) * ‖(F 0).symm b‖ := by ring
      _ = _ := by rw [hrad]; ring
  have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 9 / 16)
    (by norm_num : (9 / 16 : ℝ) < 1)).const_mul (M * (r0 / 128) * ‖(F 0).symm b‖)
  apply squeeze_zero_norm hbound
  simpa only [mul_zero] using ht

end RegularPointCoordinates

end

end OAI
