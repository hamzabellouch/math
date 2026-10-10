import OAI.Analysis.RCDHeat.VolumeComparison2
import OAI.Geometry.RCD.Metric.VolumeRigidityInput
import OAI.Geometry.RCD.Metric.ComparisonModel

namespace OAI

/-! # The small-scale Hausdorff-volume upper bound

The CD-derived Hausdorff ball estimate has an exponential factor tending
to one. It supplies the exact small-scale density input for every
nonnegative comparison curvature parameter.
-/

open Set Metric MeasureTheory Filter
open scoped Topology ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The normalized Hausdorff volume has the explicit CD exponential
upper bound, with its exact Euclidean normalization. -/
theorem NoncollapsedRCD.normalized_ball_volume_upper {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) (p : X) {r : ℝ} (hr : 0 < r) :
    (hausdorff n X).real (ball p r) ≤
      (euclideanUnitVolume n *
        Real.exp (2*r*Real.sqrt (|K|/((n:ℝ)-1))) ^ n) * r ^ n := by
  have h := hX.ball_upper K n hn p r hr
  have ht : (volume (ball (0 : Euclidean n) 1) / (2:ℝ≥0∞)^n) *
      ENNReal.ofReal (2*r*Real.exp (2*r*Real.sqrt (|K|/((n:ℝ)-1))))^n ≠ ∞ := by
    exact ENNReal.mul_ne_top (hausdorff_normalization_pos_ne_top n).2
      (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  have hh := ENNReal.toReal_mono ht h
  rw [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_pow,
    ENNReal.toReal_pow, ENNReal.toReal_ofReal (by positivity)] at hh
  norm_num only [ENNReal.toReal_ofNat] at hh
  change (hausdorff n X).real (ball p r) ≤ _ at hh
  calc
    _ ≤ _ := hh
    _ = _ := by
      unfold euclideanUnitVolume Measure.real
      rw [mul_pow, mul_pow]
      field_simp

/-- The CD Hausdorff estimate implies the exact small-scale volume upper
bound for every nonnegative comparison curvature parameter. -/
theorem NoncollapsedRCD.smallScaleVolumeUpper {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) {a : ℝ} (ha : 0 ≤ a) (p : X) :
    SmallScaleVolumeUpper (hausdorff n X) (comparisonModelVolume (n-1) a)
      p (euclideanUnitVolume n) := by
  intro δ hδ R hR
  let s : ℕ → ℝ := fun i => 1 / ((i:ℝ)+1)
  have hs (i : ℕ) : 0 < s i := by dsimp [s]; positivity
  have hszero : Tendsto s atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have harg : Tendsto (fun i => 2*s i*Real.sqrt (|K|/((n:ℝ)-1)))
      atTop (𝓝 0) := by
    simpa only [mul_zero, zero_mul] using
      (hszero.const_mul 2).mul_const (Real.sqrt (|K|/((n:ℝ)-1)))
  have hexp := (Real.continuous_exp.tendsto 0).comp harg
  have hlim : Tendsto (fun i => euclideanUnitVolume n *
      Real.exp (2*s i*Real.sqrt (|K|/((n:ℝ)-1))) ^ n)
      atTop (𝓝 (euclideanUnitVolume n)) := by
    simpa only [Real.exp_zero, one_pow, mul_one, Function.comp_def] using
      (hexp.pow n).const_mul (euclideanUnitVolume n)
  have hcoef := hlim.eventually (gt_mem_nhds
    (show euclideanUnitVolume n < euclideanUnitVolume n + δ by linarith))
  have hsmall := hszero.eventually (gt_mem_nhds hR)
  obtain ⟨i, hi, hiR⟩ := (hcoef.and hsmall).exists
  refine ⟨s i, hs i, hiR, ?_⟩
  calc
    _ ≤ (euclideanUnitVolume n *
        Real.exp (2*s i*Real.sqrt (|K|/((n:ℝ)-1))) ^ n) * (s i)^n :=
      hX.normalized_ball_volume_upper hn p (hs i)
    _ ≤ (euclideanUnitVolume n + δ) * (s i)^n :=
      mul_le_mul_of_nonneg_right hi.le (pow_nonneg (hs i).le _)
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by linarith [euclideanUnitVolume_pos n])
      have he : n-1+1 = n := by omega
      simpa only [he] using (comparisonModelVolume_bounds (n-1) ha (hs i).le).1

end RegularPointCoordinates

end

end OAI
