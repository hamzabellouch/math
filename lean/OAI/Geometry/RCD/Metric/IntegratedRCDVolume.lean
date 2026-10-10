import OAI.Geometry.RCD.Coordinates.VolumeRegularity
import OAI.Geometry.RCD.Harmonic.IntegratedRadialDensity
import OAI.Geometry.RCD.Harmonic.SmallRadialVolume

namespace OAI

/-! # Integrating the actual RCD radial area comparison down to radius zero -/

open Set Metric MeasureTheory Filter
open scoped Topology

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.hyperbolic_integral_ball_comparison {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) (hK : K < 0) (p : X)
    {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R) :
    let a := Real.sqrt (-K / ((n : ℝ) - 1))
    (hausdorff n X).real (ball p R) * (∫ t in 0..r, Real.sinh (t * a) ^ (n - 1)) ≤
      (hausdorff n X).real (ball p r) * (∫ t in 0..R, Real.sinh (t * a) ^ (n - 1)) := by
  dsimp only
  let a := Real.sqrt (-K / ((n : ℝ) - 1))
  let V : ℝ → ℝ := fun t => (hausdorff n X).real (ball p t)
  let w : ℝ → ℝ := fun t => Real.sinh (t * a) ^ (n - 1)
  let W : ℝ → ℝ := fun t => ∫ s in 0..t, w s
  have hw : Continuous w := by dsimp only [w]; fun_prop
  have hW : Continuous W := intervalIntegral.continuous_primitive
    (fun b c => hw.intervalIntegrable b c) 0
  let ε : ℕ → ℝ := fun i => (r / 2) * (1 / ((i : ℝ) + 1))
  have hε (i : ℕ) : 0 < ε i := by dsimp only [ε]; positivity
  have hεr (i : ℕ) : ε i ≤ r := by
    have hh : 1 / ((i : ℝ) + 1) ≤ 1 := (div_le_one (by positivity)).mpr (by
      have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg i
      linarith only [hi])
    dsimp only [ε]
    exact (mul_le_mul_of_nonneg_left hh (by linarith : 0 ≤ r / 2)).trans
      (by linarith : r / 2 * 1 ≤ r)
  have hεzero : Tendsto ε atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (r / 2)
  have hVε : Tendsto (fun i => V (ε i)) atTop (𝓝 0) :=
    hX.ball_volume_tendsto_zero hn p hε hεzero
  have hWε : Tendsto (fun i => W (ε i)) atTop (𝓝 0) := by
    simpa only [W, intervalIntegral.integral_same, Function.comp_def] using
      hW.continuousAt.tendsto.comp hεzero
  have hWr (i : ℕ) : (∫ t in ε i..r, w t) = W r - W (ε i) := by
    have hh := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (hw.intervalIntegrable 0 (ε i)) (hw.intervalIntegrable (ε i) r)
    change W (ε i) + (∫ t in ε i..r, w t) = W r at hh
    linarith only [hh]
  have hWR (i : ℕ) : (∫ t in ε i..R, w t) = W R - W (ε i) := by
    have hh := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (hw.intervalIntegrable 0 (ε i)) (hw.intervalIntegrable (ε i) R)
    change W (ε i) + (∫ t in ε i..R, w t) = W R at hh
    linarith only [hh]
  have hi (i : ℕ) : (V R - V (ε i)) * (W r - W (ε i)) ≤
      (V r - V (ε i)) * (W R - W (ε i)) := by
    have hc := integrated_radial_density_ratio (hεr i) hrR hw
      (hX.ball_volume_absolutelyContinuous hn p (hε i) ((hεr i).trans hrR))
    have hc' := hc (fun x hx y hy hdx hdy => by
      by_cases hxy : x < y
      · exact hX.radial_derivative_comparison hn hK p ((hε i).trans_le hx.1) hxy
          hdx.hasDerivAt hdy.hasDerivAt
      · have heq : x = y := le_antisymm (hx.2.trans hy.1) (le_of_not_gt hxy)
        subst y
        exact le_rfl)
    rw [hWr i, hWR i] at hc'
    exact hc'
  have hleft : Tendsto (fun i => (V R - V (ε i)) * (W r - W (ε i))) atTop
      (𝓝 ((V R - 0) * (W r - 0))) :=
    (tendsto_const_nhds.sub hVε).mul (tendsto_const_nhds.sub hWε)
  have hright : Tendsto (fun i => (V r - V (ε i)) * (W R - W (ε i))) atTop
      (𝓝 ((V r - 0) * (W R - 0))) :=
    (tendsto_const_nhds.sub hVε).mul (tendsto_const_nhds.sub hWε)
  have hfinal : V R * W r ≤ V r * W R := by
    simpa only [sub_zero] using
      le_of_tendsto_of_tendsto hleft hright (Eventually.of_forall hi)
  exact hfinal

end RegularPointCoordinates

end OAI
