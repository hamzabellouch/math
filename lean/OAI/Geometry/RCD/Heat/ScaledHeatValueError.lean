import OAI.Geometry.RCD.Heat.KernelHeatLipschitzDisplacement

namespace OAI

/-! # Radius-normalized heat smoothing error -/

open Set Filter MeasureTheory Metric
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.scaled_heat_value_error {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2≤n) (hK : K≤0)
    {ker : ℝ → X → X → ℝ} (hk : IsContinuousHeatKernel (hausdorff n X) hX.quadratic ker)
    (f : Lp ℝ 2 (hausdorff n X)) {φ : X → ℝ} {L : ℝ≥0}
    (hφ : LipschitzWith L φ) (hc : HasCompactSupport φ) (hf : φ =ᵐ[hausdorff n X] f)
    {r η : ℝ} (hr : 0<r) (hη : 0<η) (hη1 : η≤1) (hcurv : (-K)*r^2≤1) (x : X) :
    |kernelHeat (hausdorff n X) hX.quadratic hk (η*r^2) f x-φ x|/r≤
      Real.sqrt η*((L:ℝ)^2/2+(n:ℝ)*Real.exp 1) := by
  have ht : 0<η*r^2 := mul_pos hη (sq_pos_of_pos hr)
  have he : -K*(η*r^2)≤1 := by
    calc
      _=η*((-K)*r^2) := by ring
      _≤η*1 := mul_le_mul_of_nonneg_left hcurv hη.le
      _≤1 := by simpa only [mul_one] using hη1
  have hh := hX.kernel_heat_lipschitz_displacement hn hK hk f hφ hc hf ht x
  have hs : Real.sqrt (η*r^2)=Real.sqrt η*r := by rw [Real.sqrt_mul hη.le,Real.sqrt_sq hr.le]
  rw [hs] at hh
  have hb : Real.sqrt η*r*((L:ℝ)^2/2+(n:ℝ)*Real.exp (-K*(η*r^2)))≤
      Real.sqrt η*r*((L:ℝ)^2/2+(n:ℝ)*Real.exp 1) :=
    mul_le_mul_of_nonneg_left (add_le_add le_rfl
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (Nat.cast_nonneg n)))
      (mul_nonneg (Real.sqrt_nonneg _) hr.le)
  apply (div_le_iff₀ hr).mpr
  exact hh.trans (by convert hb using 1; ring)

end RegularPointCoordinates

end

end OAI
