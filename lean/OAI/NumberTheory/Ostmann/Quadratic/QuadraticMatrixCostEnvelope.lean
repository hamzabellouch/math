import OAI.NumberTheory.Ostmann.Quadratic.QuadraticTwoScaleCost
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticSmallKernelEnvelope

namespace OAI

/-! # The two shortened matrix factors satisfy the recursive error bounds -/

namespace Ostmann

theorem quadratic_first_matrix_cost {M N B u v Y : ℝ}
    (hM : 0 < M) (hN : 0 < N) (hB : 0 < B)
    (hu : 1 ≤ u) (hv : 1 ≤ v) (hY : 0 ≤ Y) :
    (M / N * Real.sqrt (u * v) *
      min 1 (N / (Real.sqrt M * Real.sqrt B * (u * v)))) *
      (Real.sqrt (Y + N / u) * Real.sqrt (Y + N / v)) ≤
        4 * (M + Real.sqrt M / Real.sqrt B * Y) := by
  let S := M / N * Real.sqrt (u * v) *
    min 1 (N / (Real.sqrt M * Real.sqrt B * (u * v)))
  let Z := Y + Real.sqrt (Y * N) + N / Real.sqrt (u * v)
  have hP : 1 ≤ u * v := one_le_mul_of_one_le_of_one_le hu hv
  have hP₀ : 0 < u * v := zero_lt_one.trans_le hP
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hcost : Real.sqrt (Y + N / u) * Real.sqrt (Y + N / v) ≤ 2 * Z := by
    apply (quadratic_two_scale_sqrt_cost hY hN.le hu hv).trans
    dsimp [Z]
    nlinarith [Real.sqrt_nonneg (Y * N), div_nonneg hN.le (Real.sqrt_nonneg (u * v))]
  have he := quadratic_comparison_envelope hM hN hB hP hY
  change S * Z ≤ 2 * (M + Real.sqrt M / Real.sqrt B * Y) at he
  change S * (Real.sqrt (Y + N / u) * Real.sqrt (Y + N / v)) ≤ _
  calc
    _ ≤ S * (2 * Z) := mul_le_mul_of_nonneg_left hcost hS
    _ = 2 * (S * Z) := by ring
    _ ≤ 2 * (2 * (M + Real.sqrt M / Real.sqrt B * Y)) :=
      mul_le_mul_of_nonneg_left he (by norm_num)
    _ = _ := by ring

theorem quadratic_second_matrix_cost {M N B u v Y D : ℝ}
    (hM : 0 < M) (hN : 0 ≤ N) (hB : 0 < B)
    (hu : 1 ≤ u) (hv : 1 ≤ v) (hY : 0 ≤ Y) (hD : 0 ≤ D)
    (hcut : Real.sqrt M / (Real.sqrt B * (u * v)) ≤ D) :
    (Real.sqrt M / (Real.sqrt B * Real.sqrt (u * v))) *
      (Real.sqrt (Y + N / u) * Real.sqrt (Y + N / v)) ≤
        4 * (Real.sqrt M / Real.sqrt B * Y + D * N) := by
  let S := Real.sqrt M / (Real.sqrt B * Real.sqrt (u * v))
  let Z := Y + Real.sqrt (Y * N) + N / Real.sqrt (u * v)
  have hP : 1 ≤ u * v := one_le_mul_of_one_le_of_one_le hu hv
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hcost : Real.sqrt (Y + N / u) * Real.sqrt (Y + N / v) ≤ 2 * Z := by
    apply (quadratic_two_scale_sqrt_cost hY hN hu hv).trans
    dsimp [Z]
    nlinarith [Real.sqrt_nonneg (Y * N), div_nonneg hN (Real.sqrt_nonneg (u * v))]
  have he := quadratic_small_kernel_envelope hM hN hB hP hY hD hcut
  change S * Z ≤ 2 * (Real.sqrt M / Real.sqrt B * Y + D * N) at he
  change S * (Real.sqrt (Y + N / u) * Real.sqrt (Y + N / v)) ≤ _
  calc
    _ ≤ S * (2 * Z) := mul_le_mul_of_nonneg_left hcost hS
    _ = 2 * (S * Z) := by ring
    _ ≤ 2 * (2 * (Real.sqrt M / Real.sqrt B * Y + D * N)) :=
      mul_le_mul_of_nonneg_left he (by norm_num)
    _ = _ := by ring

end Ostmann

end OAI
