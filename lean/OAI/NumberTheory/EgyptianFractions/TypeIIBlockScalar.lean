import Mathlib

namespace OAI
namespace Problem337.TypeIIBlockScalar

/-- The scalar aggregation for one dyadic Vaughan Type-II block. All analytic
information is explicit in the three elementary size bounds. -/
theorem block_bound (X M T Q U V H : ℝ)
    (hX : 0 ≤ X) (hM : 0 ≤ M) (hT : 0 ≤ T)
    (hQ : 0 < Q) (hU : 0 < U) (hV : 0 < V) (hH : 1 ≤ H)
    (hMT : M * T ≤ X) (hTU : T ≤ 2 * X / U) (hMV : M ≤ X / V) :
    (2 * M * H ^ 3) * ((2 * T / Q + 1) * (2 * M + 4 * Q * H)) *
        (T * H ^ 2) ≤
      32 * X * H ^ 6 * (X / Q + X / U + X / V + Q) := by
  have hH0 : 0 ≤ H := by linarith
  have hXQ : 0 ≤ X / Q := div_nonneg hX hQ.le
  have hXU : 0 ≤ X / U := div_nonneg hX hU.le
  have hXV : 0 ≤ X / V := div_nonneg hX hV.le
  have hMTQ : M * T / Q ≤ X / Q := div_le_div_of_nonneg_right hMT hQ.le
  have hTH : T * H ≤ (2 * X / U) * H := mul_le_mul_of_nonneg_right hTU hH0
  have hQH : X / Q ≤ H * (X / Q) := by nlinarith [mul_le_mul_of_nonneg_right hH hXQ]
  have hVH : X / V ≤ H * (X / V) := by nlinarith [mul_le_mul_of_nonneg_right hH hXV]
  have hinner : (2 * T / Q + 1) * (2 * M + 4 * Q * H) ≤
      16 * H * (X / Q + X / U + X / V + Q) := by
    have heq : (2 * T / Q + 1) * (2 * M + 4 * Q * H) =
        4 * (M * T / Q) + 8 * T * H + 2 * M + 4 * Q * H := by
      field_simp
      ring
    rw [heq]
    have hTH' : T * H ≤ 2 * (X / U) * H := by convert hTH using 1; ring
    nlinarith [mul_nonneg hH0 hXQ, mul_nonneg hH0 hXV, mul_nonneg hH0 hQ.le]
  have hfactor : 2 * (M * T) * H ^ 5 ≤ 2 * X * H ^ 5 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hMT (by norm_num)) (by positivity)
  have hinner0 : 0 ≤ (2 * T / Q + 1) * (2 * M + 4 * Q * H) := by positivity
  calc
    _ = (2 * (M * T) * H ^ 5) * ((2 * T / Q + 1) * (2 * M + 4 * Q * H)) := by ring
    _ ≤ (2 * X * H ^ 5) * (16 * H * (X / Q + X / U + X / V + Q)) :=
      mul_le_mul hfactor hinner hinner0 (by positivity)
    _ = _ := by ring

end Problem337.TypeIIBlockScalar

end OAI
