import OAI.Geometry.RCD.Coordinates.RegularHeatFrameGeometry
import OAI.Geometry.RCD.Coordinates.RegularInitialChart
import OAI.Geometry.RCD.Sobolev.BoundedDyadicScale

namespace OAI

/-! # The metric geometry of the actual fine heat-coordinate patches -/

open Set Metric MeasureTheory
open scoped InnerProductSpace NNReal

noncomputable section
namespace RegularPointCoordinates

/-- The net is substantially finer than the pinching mean radius, so that
all active energy centers satisfy the reverse mass-covering condition. -/
def regularNetRadius (R : ℝ) (shift i : ℕ) : ℝ := R / (2 : ℝ) ^ (shift + i + 28)

/-- The region is small enough that all pair comparison scales follow
the common heat comparison index. -/
def regularPatchRegion {X : Type*} [MetricSpace X] (p : X) (R : ℝ) (shift : ℕ) : Set X :=
  ball p (R / (2 : ℝ) ^ (shift + 10))

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

namespace RegularBilinearData

variable {K : ℝ} {n : ℕ} {hX : NoncollapsedRCD K n X} [(hausdorff n X).Regular]
  {base : X} {ker : ℝ → X → X → ℝ}
  {hk : IsContinuousHeatKernel (hausdorff n X) hX.quadratic ker} {enlargement zeta : ℝ}
  (d : RegularBilinearData hX base hk enlargement zeta)

/-- Return the published coordinate approximation to physical distance. -/
theorem exact_frame_pair_error {q z : X} (hq : q ∈ ball base (d.radius / 32))
    (j : ℕ) (hroom : dist z q ≤ 4 * ((d.radius / (2 : ℝ) ^ j) / 128)) :
    |‖coordinateFrame (d.frameAt q hq j) (d.values z - d.values q)‖ - dist q z| ≤
      zeta * ((d.radius / (2 : ℝ) ^ j) / 128) := by
  apply normalized_pair_error d.values (coordinateFrame (d.frameAt q hq j))
    (div_pos (div_pos d.radius_pos (by positivity)) (by norm_num)) ?_ hroom
  simpa only [coordinateFrame_apply, map_sub] using d.frameAt_approximation q hq j

/-- Every net neighbor lies in the core of the cutoff expressed in the
actual frozen heat coordinates. -/
theorem net_near_pair_bound {q z : X} (hq : q ∈ ball base (d.radius / 32))
    (hzeta : zeta ≤ 1 / 64) (i : ℕ)
    (hroom : dist z q ≤ regularNetRadius d.radius d.shift i) :
    ‖d.frozenAt q i (d.values z - d.values q)‖ ≤ 2 * regularNetRadius d.radius d.shift i := by
  let r := regularNetRadius d.radius d.shift i
  have hr : 0 < r := div_pos d.radius_pos (by positivity)
  have heq : (d.radius / (2 : ℝ) ^ (d.shift + i + 17)) / 128 = 16 * r := by
    dsimp only [r, regularNetRadius]
    rw [show d.shift + i + 28 = (d.shift + i + 17) + 11 by omega, pow_add]
    norm_num
    ring
  have hroom' : dist z q ≤ 4 * ((d.radius / (2 : ℝ) ^ (d.shift + i + 17)) / 128) := by
    rw [heq]
    change dist z q ≤ r at hroom
    linarith
  have h := d.exact_frame_pair_error hq (d.shift + i + 17) hroom'
  rw [heq] at h
  have hu := (abs_le.mp h).2
  have hf := (d.mean_heat_frame_comparison q hq (d.shift + i + 17) (by omega)
    (d.values z - d.values q)).2
  change ‖d.frozenAt q i (d.values z - d.values q)‖ ≤
    (3 / 2 : ℝ) * ‖coordinateFrame (d.frameAt q hq (d.shift + i + 17)) (d.values z - d.values q)‖ at hf
  have hs := mul_le_mul_of_nonneg_right hzeta (show 0 ≤ 16 * r by positivity)
  change _ ≤ 2 * r
  rw [dist_comm q z] at hu
  linarith

end RegularBilinearData
end RegularPointCoordinates

end

end OAI
