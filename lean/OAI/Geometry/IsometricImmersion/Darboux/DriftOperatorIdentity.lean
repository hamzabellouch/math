import OAI.Geometry.IsometricImmersion.Flows.FlowHeightCoefficients

namespace OAI

noncomputable section
open Set
open scoped ContDiff

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.Geometry.HessianCalculus

variable {q u a : Coord → ℝ} {U : Set Coord} {p : Coord}

theorem coordinateDrift_twice_expanded
    (hq : ContDiffOn ℝ ∞ q U) (hu : ContDiffOn ℝ ∞ u U)
    (hU : IsOpen U) (hp : p ∈ U) :
    coordinateDrift q (coordinateDrift q u) p =
      coordPartial 0 (coordPartial 0 u) p -
        2 * q p * coordPartial 0 (coordPartial 1 u) p +
        (q p)^2 * coordPartial 1 (coordPartial 1 u) p -
        coordinateDrift q q p * coordPartial 1 u p := by
  have hqd : DifferentiableAt ℝ q p :=
    (hq.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  have hud (i : Fin 2) : DifferentiableAt ℝ (coordPartial i u) p :=
    ((partial_contDiffOn hu hU i).contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  have hprod : DifferentiableAt ℝ (fun r => q r * coordPartial 1 u r) p := hqd.mul (hud 1)
  have hd (i : Fin 2) : coordPartial i (coordinateDrift q u) p =
      coordPartial i (coordPartial 0 u) p -
        (coordPartial i q p * coordPartial 1 u p + q p * coordPartial i (coordPartial 1 u) p) := by
    change coordPartial i (fun r => coordPartial 0 u r - q r * coordPartial 1 u r) p = _
    rw [coordPartial_sub_at (hud 0) hprod i, coordPartial_mul_at hqd (hud 1) i]
  change coordPartial 0 (coordinateDrift q u) p - q p * coordPartial 1 (coordinateDrift q u) p = _
  rw [hd 0, hd 1, coordPartial_comm hu hU hp 1 0]
  unfold coordinateDrift
  ring

theorem driftOperator_linearized_identity
    (hq : ContDiffOn ℝ ∞ q U) (hu : ContDiffOn ℝ ∞ u U)
    (ha : ContDiffOn ℝ ∞ a U) (hU : IsOpen U) (hp : p ∈ U)
    (Px Py : Coord → ℝ) (ell : ℕ) :
    driftOperator q a
      (fun r => -Px r - 2 * (ell : ℝ) * coordPartial 1 q r)
      (fun r => coordinateDrift q q r - Px r * q r - Py r +
        (ell : ℝ) * coordPartial 1 a r) u p =
      coordPartial 0 (coordPartial 0 u) p -
        2 * q p * coordPartial 0 (coordPartial 1 u) p +
        ((q p)^2 + a p) * coordPartial 1 (coordPartial 1 u) p -
        Px p * coordPartial 0 u p - Py p * coordPartial 1 u p -
        (ell : ℝ) * (2 * coordPartial 1 q p * coordPartial 0 u p -
          coordPartial 1 (fun r => (q r)^2 + a r) p * coordPartial 1 u p) := by
  have hqd : DifferentiableAt ℝ q p :=
    (hq.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  have had : DifferentiableAt ℝ a p :=
    (ha.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  have hqq : DifferentiableAt ℝ (fun r => q r * q r) p := hqd.mul hqd
  have htotal : coordPartial 1 (fun r => (q r)^2 + a r) p =
      2 * q p * coordPartial 1 q p + coordPartial 1 a p := by
    simp only [pow_two]
    rw [coordPartial_add_at hqq had 1, coordPartial_mul_at hqd hqd 1]
    ring
  unfold driftOperator
  rw [coordinateDrift_twice_expanded hq hu hU hp, htotal]
  unfold coordinateDrift
  ring

end SmoothLocal.Flow

end

end OAI
