import OAI.Geometry.RCD.Coordinates.RegularWorkingChart
import OAI.Geometry.RCD.Coordinates.CoordinateEllipsoids

namespace OAI

/-! # Actual frozen ellipsoids inside the working coordinate image -/

open Set Metric MeasureTheory
open scoped InnerProductSpace

noncomputable section
namespace RegularPointCoordinates

def regularEllipsoidRadius (R : ℝ) (shift i : ℕ) : ℝ :=
  iterationRadius (R / 128) (shift + i + 17)

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- The constructive quarter-scale corrections fill a small ellipsoid
in the actual fine heat metric. Every preimage lies in the patch region. -/
theorem regular_frozen_ellipsoid_preimages {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular]
    {base : X} {a κ B J C A Cχ enlargement zeta eta : ℝ}
    {ker : ℝ → X → X → ℝ}
    {hk : IsContinuousHeatKernel (hausdorff n X) hX.quadratic ker}
    (e : RegularProjectionEnvironment hX base hk a κ B J C A Cχ enlargement zeta eta)
    (hzeta : 0 ≤ zeta) (hzetaSmall : zeta ≤ 1 / 2048)
    (hgramSmall : (n : ℝ) ^ 2 * (((5 / 3 : ℝ) * ((1 / 4 : ℝ) ^ n)⁻¹) * zeta) ≤ 3 / 4)
    (i : ℕ) {q : X} (hq : q ∈ e.heat.patchRegion)
    (hball : ball q (4 * regularEllipsoidRadius e.heat.radius e.heat.shift i) ⊆ e.heat.patchRegion) :
    ∀ P : Euclidean n,
      ‖e.heat.frozenAt q i (P - e.heat.values q)‖ <
        regularEllipsoidRadius e.heat.radius e.heat.shift i / 32 →
      ∃ y ∈ e.heat.patchRegion,
        dist q y < regularEllipsoidRadius e.heat.radius e.heat.shift i ∧ e.heat.values y = P := by
  let d := regular_open_coordinate_data hX e hzeta hzetaSmall hgramSmall
  have hr : 0 < e.heat.radius / 128 := div_pos e.heat.radius_pos (by norm_num)
  have hc : ContinuousOn e.heat.values (ball base (e.heat.radius / 1024)) :=
    e.heat.splitting.continuous.mono (ball_subset_ball (by linarith [e.heat.radius_pos]))
  have hpre := dyadic_ellipsoid_preimages d hr (by positivity) hc
    (e.heat.shift + i + 17) q (e.heat.frozenAt q i)
    (hball.trans e.heat.patch_region_subset_initial)
    (by
      intro w
      have hq' := e.heat.patch_region_subset hq
      change ‖e.heat.quarterFrame ((e.heat.shift + i + 17) / 2) q w‖ ≤ _
      rw [e.heat.quarterFrame_eq _ q hq']
      exact e.heat.coarse_frame_le_frozen hq' i (2 * ((e.heat.shift + i + 17) / 2))
        (by omega) (by omega) w)
  intro P hP
  obtain ⟨y, _, hy, heq⟩ := hpre P hP
  refine ⟨y, hball ?_, hy, heq⟩
  have hρ : 0 < regularEllipsoidRadius e.heat.radius e.heat.shift i :=
    iterationRadius_pos hr _
  change dist q y < regularEllipsoidRadius e.heat.radius e.heat.shift i at hy
  change dist y q < 4 * regularEllipsoidRadius e.heat.radius e.heat.shift i
  rw [dist_comm]
  linarith

omit [MeasurableSpace X] [BorelSpace X] [ProperSpace X] in
/-- The inner original-space ball has room for every ellipsoid used by
the iteration, uniformly over the scale. -/
theorem regular_ellipsoid_room {R : ℝ} (hR : 0 < R) (shift i : ℕ)
    {base q : X} (hq : q ∈ ball base (R / 2 ^ (shift + 12))) :
    ball q (4 * regularEllipsoidRadius R shift i) ⊆ regularPatchRegion base R shift := by
  have hρ : 4 * regularEllipsoidRadius R shift i ≤ R / 2 ^ (shift + 12) := by
    have hp : (2 : ℝ) ^ (shift + 12) ≤ 2 ^ (shift + i + 17) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have hd := div_le_div_of_nonneg_left hR.le (by positivity) hp
    unfold regularEllipsoidRadius iterationRadius
    have hr : 0 < R / 2 ^ (shift + 12) := div_pos hR (by positivity)
    have he : R / 128 / (2 : ℝ) ^ (shift + i + 17) =
        (R / (2 : ℝ) ^ (shift + i + 17)) / 128 := by ring
    rw [he]
    linarith
  have hrad : R / 2 ^ (shift + 10) = 4 * (R / 2 ^ (shift + 12)) := by
    rw [show shift + 12 = (shift + 10) + 2 by omega, pow_add]
    norm_num
    ring
  apply ball_subset_ball'
  change 4 * regularEllipsoidRadius R shift i + dist q base ≤ R / 2 ^ (shift + 10)
  rw [hrad]
  have hdist : dist q base < R / 2 ^ (shift + 12) := hq
  have hr : 0 < R / 2 ^ (shift + 12) := div_pos hR (by positivity)
  linarith

end RegularPointCoordinates

end

end OAI
