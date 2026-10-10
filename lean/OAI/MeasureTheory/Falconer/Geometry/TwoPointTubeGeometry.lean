import OAI.MeasureTheory.Falconer.Incidence.PublishedFurstenberg
import Mathlib.Tactic

namespace OAI

/-! Two-point localization of actual bounded-chart tube parameters.
This is the elementary incidence kernel used in the multiscale Furstenberg proof. -/
namespace Falconer
open Set

theorem planar_dist_le_coordinate_sum (x y : Space 2) :
    dist x y ≤ |x 0-y 0| + |x 1-y 1| := by
  have he := EuclideanSpace.dist_sq_eq x y
  simp only [Fin.sum_univ_two, Real.dist_eq, sq_abs] at he
  nlinarith [dist_nonneg (x := x) (y := y), abs_nonneg (x 0-y 0),
    abs_nonneg (x 1-y 1), sq_abs (x 0-y 0), sq_abs (x 1-y 1),
    mul_nonneg (abs_nonneg (x 0-y 0)) (abs_nonneg (x 1-y 1))]

theorem tube_residual_le {δ : ℝ} (hδ : 0 ≤ δ) {x l : Space 2}
    (hl : |l 0| ≤ 1) (hi : TubeIncident δ x l) :
    |x 1-l 0*x 0-l 1| ≤ 2*δ := by
  have hs : 0 < Real.sqrt (1+(l 0)^2) := Real.sqrt_pos.2 (by positivity)
  have hs2 : Real.sqrt (1+(l 0)^2) ≤ 2 := by
    apply (Real.sqrt_le_left (by norm_num)).2
    have hsq := (sq_le_sq₀ (abs_nonneg (l 0)) zero_le_one).mpr hl
    nlinarith [sq_abs (l 0)]
  exact ((div_le_iff₀ hs).mp hi).trans (by nlinarith)

theorem tube_pair_residual_le {δ : ℝ} (hδ : 0 ≤ δ) {x l m : Space 2}
    (hl : |l 0| ≤ 1) (hm : |m 0| ≤ 1)
    (hil : TubeIncident δ x l) (him : TubeIncident δ x m) :
    |(l 0-m 0)*x 0+(l 1-m 1)| ≤ 4*δ := by
  calc
    _ = |(x 1-m 0*x 0-m 1)-(x 1-l 0*x 0-l 1)| := by congr 1; ring
    _ ≤ |x 1-m 0*x 0-m 1|+|x 1-l 0*x 0-l 1| := abs_sub _ _
    _ ≤ _ := by linarith [tube_residual_le hδ hm him, tube_residual_le hδ hl hil]

theorem tube_point_coordinate_lower {δ r : ℝ} (hδ : 0 ≤ δ) (_hr : 0 < r)
    (hsmall : 16*δ ≤ r) {x y l : Space 2} (hl : |l 0| ≤ 1)
    (hx : TubeIncident δ x l) (hy : TubeIncident δ y l) (hxy : r ≤ dist x y) :
    r/4 ≤ |x 0-y 0| := by
  have he : |x 1-y 1| ≤ |x 0-y 0|+4*δ := by
    calc
      _ = |l 0*(x 0-y 0)+(x 1-l 0*x 0-l 1)-(y 1-l 0*y 0-l 1)| := by congr 1; ring
      _ ≤ |l 0*(x 0-y 0)+(x 1-l 0*x 0-l 1)|+|y 1-l 0*y 0-l 1| := abs_sub _ _
      _ ≤ |l 0| * |x 0-y 0|+|x 1-l 0*x 0-l 1|+|y 1-l 0*y 0-l 1| := by
        rw [← abs_mul]
        linarith [abs_add_le (l 0*(x 0-y 0)) (x 1-l 0*x 0-l 1)]
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_right hl (abs_nonneg (x 0-y 0))
        linarith [tube_residual_le hδ hl hx, tube_residual_le hδ hl hy]
  linarith [planar_dist_le_coordinate_sum x y]

theorem two_point_tube_parameters_close {δ r : ℝ} (hδ : 0 ≤ δ)
    (hr : 0 < r) (hr1 : r ≤ 1) (hsmall : 16*δ ≤ r)
    {x y l m : Space 2} (hx0 : |x 0| ≤ 1)
    (hl : |l 0| ≤ 1) (hm : |m 0| ≤ 1)
    (hxl : TubeIncident δ x l) (hyl : TubeIncident δ y l)
    (hxm : TubeIncident δ x m) (hym : TubeIncident δ y m)
    (hxy : r ≤ dist x y) : dist l m ≤ 80*δ/r := by
  have hcoord := tube_point_coordinate_lower hδ hr hsmall hl hxl hyl hxy
  have hs : |l 0-m 0| * |x 0-y 0| ≤ 8*δ := by
    calc
      _ = |((l 0-m 0)*x 0+(l 1-m 1))-((l 0-m 0)*y 0+(l 1-m 1))| := by
        rw [← abs_mul]; congr 1; ring
      _ ≤ |(l 0-m 0)*x 0+(l 1-m 1)|+|(l 0-m 0)*y 0+(l 1-m 1)| := abs_sub _ _
      _ ≤ _ := by linarith [tube_pair_residual_le hδ hl hm hxl hxm,
        tube_pair_residual_le hδ hl hm hyl hym]
  have hslope : |l 0-m 0| ≤ 32*δ/r := by
    apply (le_div_iff₀ hr).2
    have hh := mul_le_mul_of_nonneg_left hcoord (abs_nonneg (l 0-m 0))
    nlinarith
  have hinter : |l 1-m 1| ≤ |l 0-m 0|+4*δ := by
    calc
      _ = |((l 0-m 0)*x 0+(l 1-m 1))-(l 0-m 0)*x 0| := by congr 1; ring
      _ ≤ |(l 0-m 0)*x 0+(l 1-m 1)|+|(l 0-m 0)*x 0| := abs_sub _ _
      _ ≤ _ := by
        rw [abs_mul]
        have hh := mul_le_mul_of_nonneg_left hx0 (abs_nonneg (l 0-m 0))
        linarith [tube_pair_residual_le hδ hl hm hxl hxm]
  apply (le_div_iff₀ hr).2
  have hdist : dist l m ≤ 2*|l 0-m 0|+4*δ :=
    (planar_dist_le_coordinate_sum l m).trans (by linarith [hinter])
  have hsum := mul_le_mul_of_nonneg_right hdist hr.le
  have hsl := (le_div_iff₀ hr).mp hslope
  have hd := mul_le_mul_of_nonneg_left hr1 hδ
  nlinarith

end Falconer

end OAI
