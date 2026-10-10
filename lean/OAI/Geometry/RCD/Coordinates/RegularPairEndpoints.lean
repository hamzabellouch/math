import OAI.Geometry.RCD.Coordinates.RegularEllipsoids

namespace OAI

/-! # Ambient pair separation at the scale selected by the iteration -/

open Set Metric MeasureTheory
open scoped InnerProductSpace

noncomputable section
namespace RegularPointCoordinates

theorem source_eq_ellipsoidRadius (R : ℝ) (shift i : ℕ) :
    distanceSourceRadius R (shift + i) = 8388608 * regularEllipsoidRadius R shift i := by
  unfold distanceSourceRadius regularEllipsoidRadius iterationRadius
  rw [show shift + i + 17 = (shift + i + 1) + 16 by omega, pow_add]
  norm_num
  ring

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

namespace RegularBilinearData

variable {K : ℝ} {n : ℕ} {hX : NoncollapsedRCD K n X} [(hausdorff n X).Regular]
  {base : X} {ker : ℝ → X → X → ℝ}
  {hk : IsContinuousHeatKernel (hausdorff n X) hX.quadratic ker} {enlargement zeta : ℝ}
  (d : RegularBilinearData hX base hk enlargement zeta)

/-- The precise approximation error is small relative to the original
ambient pair distance at the chosen dyadic scale. -/
theorem pair_endpoints_at_scale {L : ℝ} (hL : 2097152 ≤ L)
    (hzeta : 0 ≤ zeta) (hzetaL : zeta * L ≤ 2097152)
    (i : ℕ) {q z : X} (hq : q ∈ ball base (d.radius / 32))
    (hlow : L * dist q z ≤ distanceSourceRadius d.radius (d.shift + i))
    (hupp : distanceSourceRadius d.radius (d.shift + i) ≤ 2 * L * dist q z) :
    (1 / 4 : ℝ) * dist q z ≤ ‖d.frozenAt q i (d.values z - d.values q)‖ ∧
    ‖d.frozenAt q i (d.values z - d.values q)‖ ≤ 4 * dist q z := by
  let rho := regularEllipsoidRadius d.radius d.shift i
  have heq := source_eq_ellipsoidRadius d.radius d.shift i
  change distanceSourceRadius d.radius (d.shift + i) = 8388608 * rho at heq
  have haux : (d.radius / (2 : ℝ) ^ (d.shift + i + 17)) / 128 = rho := by
    unfold rho regularEllipsoidRadius iterationRadius
    ring
  have hroom : dist z q ≤ 4 * ((d.radius / (2 : ℝ) ^ (d.shift + i + 17)) / 128) := by
    rw [dist_comm, haux]
    rw [heq] at hlow
    have h := mul_le_mul_of_nonneg_right hL (dist_nonneg (x := q) (y := z))
    linarith
  have herr : zeta * rho ≤ dist q z / 2 := by
    have hu := mul_le_mul_of_nonneg_left hupp hzeta
    have hh := mul_le_mul_of_nonneg_right hzetaL (dist_nonneg (x := q) (y := z))
    rw [heq] at hu
    nlinarith only [hu, hh]
  have happ := d.exact_frame_pair_error hq (d.shift + i + 17) hroom
  rw [haux] at happ
  have hm := d.mean_heat_frame_comparison q hq (d.shift + i + 17) (by omega) (d.values z - d.values q)
  change ‖coordinateFrame (d.frameAt q hq (d.shift + i + 17)) (d.values z - d.values q)‖ ≤
    (3 / 2 : ℝ) * ‖d.frozenAt q i (d.values z - d.values q)‖ ∧
    ‖d.frozenAt q i (d.values z - d.values q)‖ ≤
      (3 / 2 : ℝ) * ‖coordinateFrame (d.frameAt q hq (d.shift + i + 17)) (d.values z - d.values q)‖ at hm
  constructor <;> linarith [(abs_le.mp happ).1, (abs_le.mp happ).2,
    dist_nonneg (x := q) (y := z)]

end RegularBilinearData
end RegularPointCoordinates

end

end OAI
