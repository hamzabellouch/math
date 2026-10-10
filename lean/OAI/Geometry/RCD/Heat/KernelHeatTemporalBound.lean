import OAI.Geometry.RCD.Heat.KernelTwoTimeAbsoluteSlope
import OAI.Geometry.RCD.Heat.KernelHeatTimeContinuity
import OAI.Geometry.RCD.Harmonic.TimeQuadraticRate

namespace OAI

/-! # The dimensional temporal square bound for actual weak-Laplacian data -/

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.kernel_heat_temporal_bound_of_derivative
    (K : ℝ) (n : ℕ) [(hausdorff n X).Regular] (hn : 2 ≤ n)
    (hX : NoncollapsedRCD K n X) (hK : K ≤ 0) {N : ℝ} (hN : (n:ℝ) ≤ N)
    {ker : ℝ → X → X → ℝ} (hk : IsContinuousHeatKernel (hausdorff n X) hX.quadratic ker)
    (f : Lp ℝ 2 (hausdorff n X))
    {φ : X → ℝ} {L : ℝ≥0} (hφ : LipschitzWith L φ)
    (p : X) (R : ℝ) (hsupp : ∀ x, R < dist p x → φ x = 0)
    (hf : φ =ᵐ[hausdorff n X] f)
    (H : Lp ℝ 2 (hausdorff n X)) {r : ℝ} (hr : 0 < r)
    (hH : (fun x => (slopeAtScale φ r x).toReal^2) =ᵐ[hausdorff n X] H)
    {t : ℝ} (ht : 0 < t) (x : X) (D : ℝ)
    (hder : HasDerivAt (fun s => kernelHeat (hausdorff n X) hX.quadratic hk s f x) D t) :
    (2*t/N)*D^2 ≤
      Real.exp (-2*K*t)*kernelHeat (hausdorff n X) hX.quadratic hk t H x := by
  let μ := hausdorff n X
  let V := fun s => kernelHeat μ hX.quadratic hk s H x
  let E := Real.exp (-2*K*t)
  have hNp : 0 < N := lt_of_lt_of_le (by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hn)) hN
  have hE : 0 < E := Real.exp_pos _
  have hVc : ContinuousAt V t := kernelHeat_continuousAt_time μ hX.quadratic hk H ht x
  have hquad (α : ℝ) : 0 ≤ V t/2+E*N*α^2/(4*t)-α*D := by
    have hl := timeQuadraticRate_tendsto ht hder hVc K N α
    apply ge_of_tendsto hl
    have hs : Tendsto (fun h : ℝ => t+α*h) (𝓝[>] 0) (𝓝 t) := by
      simpa only [mul_zero,add_zero] using
        ((show Continuous (fun h : ℝ => t+α*h) by fun_prop).continuousAt (x := 0)).tendsto.mono_left
          nhdsWithin_le_nhds
    have hsc : Tendsto (fun h : ℝ => 2*h*(L:ℝ)) (𝓝[>] 0) (𝓝 0) := by
      simpa only [mul_zero,zero_mul] using
        ((show Continuous (fun h : ℝ => 2*h*(L:ℝ)) by fun_prop).continuousAt (x := 0)).tendsto.mono_left
          nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin,hs.eventually (Ioi_mem_nhds ht),
      hsc.eventually (Iio_mem_nhds hr)] with h hh hs hsmall
    apply timeQuadraticRate_nonneg hh
    have hb := hX.kernel_two_time_abs_slope_bound K n hn hK hN hk hφ p R hsupp
      (f) H hf hh hsmall hH hs ht x x
    simpa only [dist_self,zero_pow (by decide : 2 ≠ 0),zero_add] using (le_abs_self _).trans hb
  let α := 2*t*D/(N*E)
  have hh := hquad α
  have heq : V t/2+E*N*α^2/(4*t)-α*D = V t/2-t*D^2/(N*E) := by
    dsimp only [α]
    field_simp
    ring
  rw [heq] at hh
  have hh' : t*D^2/(N*E) ≤ V t/2 := by linarith only [hh]
  have hm := (div_le_iff₀ (mul_pos hNp hE)).mp hh'
  change (2*t/N)*D^2 ≤ E*V t
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hNp).mpr
  nlinarith only [hm]

theorem NoncollapsedRCD.kernel_heat_temporal_bound
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
    (2*t/N)*(kernelHeat (hausdorff n X) hX.quadratic hk t d x)^2 ≤
      Real.exp (-2*K*t)*kernelHeat (hausdorff n X) hX.quadratic hk t H x := by
  exact hX.kernel_heat_temporal_bound_of_derivative K n hn hK hN hk
    (SobolevSpace.toLp (hausdorff n X) hX.quadratic u) hφ p R hsupp hf H hr hH ht x
    (kernelHeat (hausdorff n X) hX.quadratic hk t d x)
    (kernelHeat_weakLaplacian_hasDerivAt (hausdorff n X) hX.quadratic hk u d hd ht x)

end RegularPointCoordinates

end

end OAI
