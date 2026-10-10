import OAI.Geometry.RCD.Heat.KernelHeatTimeDifference

namespace OAI

/-! # A scale-uniform square-root bound for heat smoothing error -/

open Set Filter MeasureTheory Metric
open scoped Topology NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.kernel_heat_lipschitz_displacement_aux {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2≤n) (hK : K≤0)
    {ker : ℝ → X → X → ℝ} (hk : IsContinuousHeatKernel (hausdorff n X) hX.quadratic ker)
    (f : Lp ℝ 2 (hausdorff n X)) {φ : X → ℝ} {L : ℝ≥0}
    (hφ : LipschitzWith L φ) (p : X) (R : ℝ) (hsupp : ∀ x, R<dist p x → φ x=0)
    (hf : φ =ᵐ[hausdorff n X] f) {σ t : ℝ} (hσ : 0<σ) (ht : 0<t) (x : X) :
    |kernelHeat (hausdorff n X) hX.quadratic hk t f x-φ x|≤
      σ/2*(L:ℝ)^2+Real.exp (-K*t)*(2*(n:ℝ)*t)/(2*σ) := by
  have hinit := hX.kernel_heat_initial_limit hn hk f hφ hf
    (|φ p|+(L:ℝ)*max R 0) (compact_lipschitz_abs_bound hφ p R hsupp) x
  have hleft : Tendsto (fun k => |kernelHeat (hausdorff n X) hX.quadratic hk t f x-
      kernelHeat (hausdorff n X) hX.quadratic hk (heatStep k) f x|) atTop
      (𝓝 |kernelHeat (hausdorff n X) hX.quadratic hk t f x-φ x|) :=
    (tendsto_const_nhds.sub hinit).abs
  have hcont : Continuous (fun s : ℝ => σ/2*(L:ℝ)^2+
      Real.exp (-K*(t+s))*(2*(n:ℝ)*(Real.sqrt t-Real.sqrt s)^2)/(2*σ)) := by fun_prop
  have hright := (hcont.tendsto 0).comp heatStep_tendsto
  have hh := le_of_tendsto_of_tendsto hleft hright (Eventually.of_forall (fun k =>
    hX.kernel_heat_time_difference hn hK hk f hφ p R hsupp hf hσ ht (heatStep_pos k) x))
  simpa only [add_zero,Real.sqrt_zero,sub_zero,Real.sq_sqrt ht.le] using hh

theorem NoncollapsedRCD.kernel_heat_lipschitz_displacement {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2≤n) (hK : K≤0)
    {ker : ℝ → X → X → ℝ} (hk : IsContinuousHeatKernel (hausdorff n X) hX.quadratic ker)
    (f : Lp ℝ 2 (hausdorff n X)) {φ : X → ℝ} {L : ℝ≥0}
    (hφ : LipschitzWith L φ) (hc : HasCompactSupport φ)
    (hf : φ =ᵐ[hausdorff n X] f) {t : ℝ} (ht : 0<t) (x : X) :
    |kernelHeat (hausdorff n X) hX.quadratic hk t f x-φ x|≤
      Real.sqrt t*((L:ℝ)^2/2+(n:ℝ)*Real.exp (-K*t)) := by
  obtain ⟨R,hR⟩ := hc.isCompact.isBounded.subset_closedBall x
  have hsupp (y : X) (hy : R<dist x y) : φ y=0 := by
    by_contra hh
    have hb := hR (subset_tsupport φ hh)
    have hd : dist x y≤R := by simpa only [mem_closedBall,dist_comm] using hb
    exact (not_le_of_gt hy) hd
  have hh := hX.kernel_heat_lipschitz_displacement_aux hn hK hk f hφ x R hsupp hf (Real.sqrt_pos.mpr ht) ht x
  have he : Real.exp (-K*t)*(2*(n:ℝ)*t)/(2*Real.sqrt t)=
      Real.sqrt t*((n:ℝ)*Real.exp (-K*t)) := by
    calc
      _=Real.exp (-K*t)*(n:ℝ)*(t/Real.sqrt t) := by ring
      _=_ := by rw [Real.div_sqrt]; ring
  rw [he] at hh
  convert hh using 1
  ring

end RegularPointCoordinates

end

end OAI
