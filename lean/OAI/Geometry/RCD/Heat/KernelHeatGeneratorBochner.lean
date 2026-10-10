import OAI.Geometry.RCD.Heat.KernelHeatGeneratorDerivative
import OAI.Geometry.RCD.Heat.KernelHeatScaledBochner

namespace OAI

/-! # Dimensional gradient bounds for compact Lipschitz L2 data

The time term uses the actual bounded heat generator. No weak-Laplacian
assumption on the initial datum is needed.
-/

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.kernel_heat_scaled_generator_bochner
    (K : ℝ) (n : ℕ) [(hausdorff n X).Regular] (hn : 2 ≤ n)
    (hX : NoncollapsedRCD K n X) (hK : K ≤ 0) {N : ℝ} (hN : (n:ℝ) ≤ N)
    {ker : ℝ → X → X → ℝ} (hk : IsContinuousHeatKernel (hausdorff n X) hX.quadratic ker)
    (f : Lp ℝ 2 (hausdorff n X))
    {φ : X → ℝ} {L : ℝ≥0} (hφ : LipschitzWith L φ)
    (p : X) (R : ℝ) (hsupp : ∀ x, R < dist p x → φ x = 0)
    (hf : φ =ᵐ[hausdorff n X] f)
    (H : Lp ℝ 2 (hausdorff n X)) {r : ℝ} (hr : 0 < r)
    (hH : (fun x => (slopeAtScale φ r x).toReal^2) =ᵐ[hausdorff n X] H)
    {t : ℝ} (ht : 0 < t) (x : X) :
    (localSlope (kernelHeat (hausdorff n X) hX.quadratic hk t
      (f)) x).toReal^2+
      (2*t/N)*(kernelHeatGeneratorSource (hausdorff n X) hX.quadratic hk t f x)^2 ≤
      Real.exp (-2*K*t)*kernelHeat (hausdorff n X) hX.quadratic hk t H x := by
  let μ := hausdorff n X
  let c := r/(2*((L:ℝ)+1))
  have hc : 0 < c := div_pos hr (by positivity)
  have hsmall {σ : ℝ} (hσ : 0 < σ) (hσc : σ < c) : 2*σ*(L:ℝ) < r := by
    have hh := (lt_div_iff₀ (show 0 < 2*((L:ℝ)+1) by positivity)).mp hσc
    nlinarith [L.coe_nonneg]
  have hNp : 0 < N := lt_of_lt_of_le (by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hn)) hN
  apply spaceTime_localSlope_bound hNp ht hc
    (kernelHeat_generator_hasDerivAt μ hX.quadratic hk f ht x)
    (kernelHeat_continuousAt_time μ hX.quadratic hk H ht x)
    (hX.kernel_heat_temporal_bound_of_derivative K n hn hK hN hk f hφ p R hsupp hf H hr hH ht x
      (kernelHeatGeneratorSource μ hX.quadratic hk t f x) (kernelHeat_generator_hasDerivAt μ hX.quadratic hk f ht x))
  intro s hs σ hσ hσc y
  exact hX.kernel_two_time_abs_slope_bound K n hn hK hN hk hφ p R hsupp
    (f) H hf hσ (hsmall hσ hσc) hH hs ht x y


theorem NoncollapsedRCD.kernel_heat_local_generator_bochner
    (K : ℝ) (n : ℕ) [(hausdorff n X).Regular] (hn : 2 ≤ n)
    (hX : NoncollapsedRCD K n X) (hK : K ≤ 0) {N : ℝ} (hN : (n:ℝ) ≤ N)
    {ker : ℝ → X → X → ℝ} (hk : IsContinuousHeatKernel (hausdorff n X) hX.quadratic ker)
    (f : Lp ℝ 2 (hausdorff n X))
    {φ : X → ℝ} {L : ℝ≥0} (hφ : LipschitzWith L φ)
    (p : X) (R : ℝ) (hsupp : ∀ x, R < dist p x → φ x = 0)
    (hf : φ =ᵐ[hausdorff n X] f)
    (H : Lp ℝ 2 (hausdorff n X))
    (hH : (fun x => (localSlope φ x).toReal^2) =ᵐ[hausdorff n X] H)
    {t : ℝ} (ht : 0 < t) (x : X) :
    (localSlope (kernelHeat (hausdorff n X) hX.quadratic hk t
      (f)) x).toReal^2+
      (2*t/N)*(kernelHeatGeneratorSource (hausdorff n X) hX.quadratic hk t f x)^2 ≤
      Real.exp (-2*K*t)*kernelHeat (hausdorff n X) hX.quadratic hk t H x := by
  let μ := hausdorff n X
  let Hj : ℕ → Lp ℝ 2 μ := fun j =>
    (slopeAtScale_sq_memLp μ hφ p R hsupp (by positivity : 0 ≤ 1/(j+1:ℝ))).toLp
      (fun x => (slopeAtScale φ (1/(j+1:ℝ)) x).toReal^2)
  have hHeq : (localSlope_sq_compact_memLp μ hφ p R hsupp).toLp
      (fun x => (localSlope φ x).toReal^2) = H := by
    apply Lp.ext
    exact (localSlope_sq_compact_memLp μ hφ p R hsupp).coeFn_toLp.trans hH
  have hc : Tendsto Hj atTop (𝓝 H) := by
    simpa only [hHeq] using slopeSq_toLp_tendsto μ hφ p R hsupp
  have hlim : Tendsto (fun j => Real.exp (-2*K*t)*kernelHeat μ hX.quadratic hk t (Hj j) x)
      atTop (𝓝 (Real.exp (-2*K*t)*kernelHeat μ hX.quadratic hk t H x)) := by
    exact (((show Continuous (fun f : Lp ℝ 2 μ => inner ℝ (heatKernelRow μ hX.quadratic hk t x) f)
      from continuous_const.inner continuous_id).tendsto H).comp hc).const_mul _
  apply ge_of_tendsto hlim
  apply Eventually.of_forall
  intro j
  exact hX.kernel_heat_scaled_generator_bochner K n hn hK hN hk f hφ p R hsupp hf (Hj j)
    (by positivity : 0 < 1/(j+1:ℝ))
    (slopeAtScale_sq_memLp μ hφ p R hsupp (by positivity : 0 ≤ 1/(j+1:ℝ))).coeFn_toLp.symm ht x

end RegularPointCoordinates

end

end OAI
