import OAI.Geometry.CylinderCovering.Rational.Field

namespace OAI

noncomputable section
open Filter
open scoped Topology ContDiff

namespace SlopeRational

theorem radius_radial_coordinate (r : ℝ) : radius (1 / 2 - r) = r := by
  unfold radius
  ring

theorem potential_contDiffAt (d : ℝ) {z : Plane}
    (h : radius (z 1) + d ≠ 0) :
    ContDiffAt ℝ ∞ (fun p : Plane => potential d (p 0) (p 1)) z := by
  unfold potential radius
  apply ContDiffAt.div (by fun_prop) (by fun_prop)
  exact mul_ne_zero (by norm_num) h

theorem potential_contDiffOn (d : ℝ) :
    ContDiffOn ℝ ∞ (fun p : Plane => potential d (p 0) (p 1))
      {z : Plane | -d < radius (z 1)} := by
  intro z hz
  change -d < radius (z 1) at hz
  exact (potential_contDiffAt d (by linarith : radius (z 1) + d ≠ 0)).contDiffWithinAt

theorem potential_radial_deriv_Y (d Y r : ℝ) :
    deriv (fun y => potential d y (1 / 2 - r)) Y = Y / (2 * (r + d)) := by
  simpa only [b, radius_radial_coordinate] using
    (potential_hasDerivAt_Y d Y (1 / 2 - r)).deriv

theorem potential_radial_hasDerivAt_r (d Y r : ℝ) (h : r + d ≠ 0) :
    HasDerivAt (fun s => potential d Y (1 / 2 - s))
      (a d Y (1 / 2 - r)) r := by
  have ht : radius (1 / 2 - r) + d ≠ 0 := by
    simpa only [radius_radial_coordinate] using h
  have hp := (potential_hasDerivAt_T d Y (1 / 2 - r) ht).comp r
    ((hasDerivAt_id r).const_sub (1 / 2 : ℝ))
  simpa only [Function.comp_def, neg_mul, mul_neg, mul_one, neg_neg] using hp

theorem potential_radial_hasDerivAt_YY (d Y r : ℝ) :
    HasDerivAt (fun y => deriv (fun x => potential d x (1 / 2 - r)) y)
      (1 / (2 * (r + d))) Y := by
  simp only [potential_radial_deriv_Y]
  exact (hasDerivAt_id Y).div_const (2 * (r + d))

theorem potential_radial_hasDerivAt_Yr (d Y r : ℝ) (h : r + d ≠ 0) :
    HasDerivAt (fun s => deriv (fun y => potential d y (1 / 2 - s)) Y)
      (-Y / (2 * (r + d) ^ 2)) r := by
  simp only [potential_radial_deriv_Y]
  have hp := (hasDerivAt_const r Y).div
    (((hasDerivAt_id r).add_const d).const_mul 2)
    (mul_ne_zero (by norm_num) h)
  convert hp using 1 <;> first | rfl | (dsimp; field_simp [h]; ring)

theorem potential_radial_hasDerivAt_rY (d Y r : ℝ) (h : r + d ≠ 0) :
    HasDerivAt (fun y => deriv (fun s => potential d y (1 / 2 - s)) r)
      (-Y / (2 * (r + d) ^ 2)) Y := by
  have he : (fun y => deriv (fun s => potential d y (1 / 2 - s)) r) =
      (fun y => a d y (1 / 2 - r)) := by
    funext y
    exact (potential_radial_hasDerivAt_r d y r h).deriv
  rw [he]
  simp only [a, radius_radial_coordinate]
  have hp := (((hasDerivAt_id Y).pow 2).neg.div_const (4 * (r + d) ^ 2)).sub_const
    (r * (r + 2 * d) / (16 * (r + d) ^ 2))
  convert hp using 1 <;> first | rfl | (dsimp; field_simp [h]; ring)

theorem potential_radial_hasDerivAt_rr (d Y r : ℝ) (h : r + d ≠ 0) :
    HasDerivAt (fun s => deriv (fun t => potential d Y (1 / 2 - t)) s)
      ((Y ^ 2 / 2 - d ^ 2 / 8) / (r + d) ^ 3) r := by
  have hn : ∀ᶠ s : ℝ in 𝓝 r, s + d ≠ 0 :=
    (continuousAt_id.add_const d).eventually_ne h
  have he : (fun s => deriv (fun t => potential d Y (1 / 2 - t)) s) =ᶠ[𝓝 r]
      (fun s => -1 / 16 + (d ^ 2 - 4 * Y ^ 2) / (16 * (s + d) ^ 2)) := by
    filter_upwards [hn] with s hs
    rw [(potential_radial_hasDerivAt_r d Y s hs).deriv]
    simpa only [radius_radial_coordinate] using
      (a_simplified d Y (1 / 2 - s) (by simpa only [radius_radial_coordinate] using hs))
  have hp := ((hasDerivAt_const r (d ^ 2 - 4 * Y ^ 2)).div
    ((((hasDerivAt_id r).add_const d).pow 2).const_mul 16)
    (mul_ne_zero (by norm_num) (pow_ne_zero 2 h))).const_add (-1 / 16 : ℝ)
  have hq : HasDerivAt
      (fun s => -1 / 16 + (d ^ 2 - 4 * Y ^ 2) / (16 * (s + d) ^ 2))
      ((Y ^ 2 / 2 - d ^ 2 / 8) / (r + d) ^ 3) r := by
    convert hp using 1 <;> first | rfl | (dsimp; field_simp [h]; ring)
  exact hq.congr_of_eventuallyEq he

theorem potential_radial_hessian_det (d Y r : ℝ) (h : r + d ≠ 0) :
    deriv (fun y => deriv (fun x => potential d x (1 / 2 - r)) y) Y *
        deriv (fun s => deriv (fun t => potential d Y (1 / 2 - t)) s) r -
      deriv (fun s => deriv (fun y => potential d y (1 / 2 - s)) Y) r *
        deriv (fun y => deriv (fun s => potential d y (1 / 2 - s)) r) Y =
      -d ^ 2 / (16 * (r + d) ^ 4) := by
  rw [(potential_radial_hasDerivAt_YY d Y r).deriv,
    (potential_radial_hasDerivAt_rr d Y r h).deriv,
    (potential_radial_hasDerivAt_Yr d Y r h).deriv,
    (potential_radial_hasDerivAt_rY d Y r h).deriv]
  field_simp [h]
  ring

theorem potential_zero_homogeneous (c Y r : ℝ) :
    potential 0 (c * Y) (1 / 2 - c * r) =
      c * potential 0 Y (1 / 2 - r) := by
  simp only [potential, radius_radial_coordinate, add_zero]
  by_cases hc : c = 0
  · simp [hc]
  by_cases hr : r = 0
  · simp [hr]
  field_simp [hc, hr]

theorem field_zero_ratio (Y r : ℝ) (hr : r ≠ 0) :
    a 0 Y (1 / 2 - r) = -(1 / 16 + (Y / r) ^ 2 / 4) ∧
      b 0 Y (1 / 2 - r) = (Y / r) / 2 := by
  simp only [a, b, radius_radial_coordinate, mul_zero, add_zero]
  constructor <;> field_simp [hr]
  ring

end SlopeRational

end

end OAI
