import OAI.Geometry.RCD.Heat.KernelHeatTemporalBound
import OAI.Geometry.RCD.Harmonic.SpaceTimeLocalSlope

namespace OAI

/-! # The scaled dimensional gradient estimate for actual compact regular data -/

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.kernel_heat_scaled_bochner
    (K : ℝ) (n : ℕ) [(hausdorff n X).Regular] (hn : 2 ≤ n)
    (hX : NoncollapsedRCD K n X) (hK : K ≤ 0) {N : ℝ} (hN : (n:ℝ) ≤ N)
    {ker : ℝ → X → X → ℝ} (hk : IsContinuousHeatKernel (hausdorff n X) hX.quadratic ker)
    (u : SobolevSpace (hausdorff n X) hX.quadratic) (d : Lp ℝ 2 (hausdorff n X))
    (hd : IsWeakLaplacian (hausdorff n X) hX.quadratic u d)
    {φ : X → ℝ} {L : ℝ≥0} (hφ : LipschitzWith L φ)
    (p : X) (R : ℝ) (hsupp : ∀ x, R < dist p x → φ x = 0)
    (hf : φ =ᵐ[hausdorff n X] SobolevSpace.toLp (hausdorff n X) hX.quadratic u)
    (H : Lp ℝ 2 (hausdorff n X)) {r : ℝ} (hr : 0 < r)
    (hH : (fun x => (slopeAtScale φ r x).toReal^2) =ᵐ[hausdorff n X] H)
    {t : ℝ} (ht : 0 < t) (x : X) :
    (localSlope (kernelHeat (hausdorff n X) hX.quadratic hk t
      (SobolevSpace.toLp (hausdorff n X) hX.quadratic u)) x).toReal^2+
      (2*t/N)*(kernelHeat (hausdorff n X) hX.quadratic hk t d x)^2 ≤
      Real.exp (-2*K*t)*kernelHeat (hausdorff n X) hX.quadratic hk t H x := by
  let μ := hausdorff n X
  let c := r/(2*((L:ℝ)+1))
  have hc : 0 < c := div_pos hr (by positivity)
  have hsmall {σ : ℝ} (hσ : 0 < σ) (hσc : σ < c) : 2*σ*(L:ℝ) < r := by
    have hh := (lt_div_iff₀ (show 0 < 2*((L:ℝ)+1) by positivity)).mp hσc
    nlinarith [L.coe_nonneg]
  have hNp : 0 < N := lt_of_lt_of_le (by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hn)) hN
  apply spaceTime_localSlope_bound hNp ht hc
    (kernelHeat_weakLaplacian_hasDerivAt μ hX.quadratic hk u d hd ht x)
    (kernelHeat_continuousAt_time μ hX.quadratic hk H ht x)
    (hX.kernel_heat_temporal_bound K n hn hK hN hk u d hd hφ p R hsupp hf H hr hH ht x)
  intro s hs σ hσ hσc y
  exact hX.kernel_two_time_abs_slope_bound K n hn hK hN hk hφ p R hsupp
    (SobolevSpace.toLp μ hX.quadratic u) H hf hσ (hsmall hσ hσc) hH hs ht x y

end RegularPointCoordinates

end

end OAI
