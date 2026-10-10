import Mathlib
import OAI.Analysis.RieszRectifiability.Rigidity.FractionalSchwartzKernel
import OAI.Analysis.RieszRectifiability.Kernel.LocalSchwartzSecondDifference

namespace OAI

namespace RieszRectifiability

noncomputable section

open SchwartzMap MeasureTheory Metric Filter Topology Set
open scoped NNReal ENNReal

theorem fractional_kernel_bound_from_quadratic_difference {d : ℕ}
    (p : ℕ) (g : Ambient d → ℂ) (x h : Ambient d) (M : ℝ) (hM : 0 ≤ M)
    (hb : ‖symmetricSecondDifference g x h‖ ≤ M * ‖h‖ ^ 2) :
    ‖fractionalSchwartzKernel (p + 1) g x h‖ ≤ M * inverseDistancePow p 0 h := by
  rw [fractionalSchwartzKernel, norm_smul,
    Real.norm_of_nonneg (inverseDistancePow_nonneg _ _ _)]
  by_cases hh : h = 0
  · subst h
    simp only [inverseDistancePow, dist_self, zero_pow (by omega : p + 1 + 1 ≠ 0), inv_zero, zero_mul]
    positivity
  · have hn : ‖h‖ ≠ 0 := norm_ne_zero_iff.mpr hh
    calc
      _ ≤ inverseDistancePow (p + 1 + 1) 0 h * (M * ‖h‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hb (inverseDistancePow_nonneg _ _ _)
      _ = _ := by
        simp only [inverseDistancePow, dist_zero_left, pow_succ]
        field_simp

theorem fractionalSchwartzKernel_near_spatial_decay {d : ℕ}
    (p : ℕ) (C : ℝ) (μ : Measure (Ambient d)) (hgrowth : GlobalUpperGrowth (p + 1) C μ)
    (g : 𝓢(Ambient d, ℂ)) (x : Ambient d) (hx : 0 < ‖x‖) :
    (∫ h in closedBall 0 (‖x‖ / 2), ‖fractionalSchwartzKernel (p + 1) g x h‖ ∂μ) ≤
      (4 * (C * 2 ^ (p + 1) * 2 ^ p) * 2 ^ (p + 3) *
        SchwartzMap.seminorm ℝ (p + 4) 2 g) / ‖x‖ ^ (p + 3) := by
  let R := ‖x‖ / 2
  let M := SchwartzMap.seminorm ℝ (p + 4) 2 g / R ^ (p + 4)
  have hR : 0 < R := by dsimp [R]; positivity
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hK := fractionalSchwartzKernel_integrable_of_growth p C μ hgrowth g x
  obtain ⟨hi, _⟩ := inverseDistancePow_near_integrable_and_bound p C μ hgrowth 0 R hR
  have hb' : (∫ h in closedBall 0 R, inverseDistancePow p 0 h ∂μ) ≤
      2 * (C * 2 ^ (p + 1) * 2 ^ p * R) :=
    inverseDistancePow_near_integral_bound p C μ hgrowth 0 R hR
  calc
    _ ≤ ∫ h in closedBall 0 R, (2 * M) * inverseDistancePow p 0 h ∂μ := by
      apply integral_mono_ae hK.norm.restrict (hi.const_mul _)
      filter_upwards [ae_restrict_mem measurableSet_closedBall] with h hh
      have hh' : ‖h‖ ≤ ‖x‖ / 2 := by simpa only [mem_closedBall, dist_zero_right] using! hh
      exact fractional_kernel_bound_from_quadratic_difference p g x h (2 * M) (by positivity)
        (schwartz_second_difference_spatial_bound g (p + 4) x h hx hh')
    _ = (2 * M) * ∫ h in closedBall 0 R, inverseDistancePow p 0 h ∂μ := integral_const_mul _ _
    _ ≤ (2 * M) * (2 * (C * 2 ^ (p + 1) * 2 ^ p * R)) :=
      mul_le_mul_of_nonneg_left hb' (by positivity)
    _ = _ := by
      dsimp [M, R]
      simp only [pow_add, div_pow]
      field_simp
      ring

end

end RieszRectifiability

end OAI
