import OAI.Analysis.LipschitzHilbert.Estimates.PlaneCoordinates
import OAI.Analysis.LipschitzHilbert.Geometry.FrozenDirection
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

namespace OAI

/-! A finite collection of orthogonal charts for a unit direction field.
The clipped slope is defined on the whole plane. On its orientation patch
it agrees exactly with the ratio of the two coordinates. -/
noncomputable section
open MeasureTheory
open scoped NNReal
namespace LipschitzHilbert

def horizontalUnit : Plane := EuclideanSpace.single 0 1

theorem horizontalUnit_norm : ‖horizontalUnit‖ = 1 := by
  simp [horizontalUnit, PiLp.norm_single]

def directionChart (d : Plane) : Plane ≃ₗᵢ[ℝ] Plane :=
  (ℝ ∙ (d-horizontalUnit))ᗮ.reflection

theorem directionChart_center (d : Plane) (hd : ‖d‖=1) :
    directionChart d d = horizontalUnit :=
  Submodule.reflection_sub (hd.trans horizontalUnit_norm.symm)

def chartField (d : Plane) (v : Plane → Plane) : Plane → Plane :=
  fun x => directionChart d (v ((directionChart d).symm x))

theorem chartField_lipschitz (d : Plane) {v : Plane → Plane} {K : ℝ≥0}
    (hv : LipschitzWith K v) : LipschitzWith K (chartField d v) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [chartField, LinearIsometryEquiv.dist_map] using
    hv.dist_le_mul ((directionChart d).symm x) ((directionChart d).symm y)

theorem chartField_unit (d : Plane) {v : Plane → Plane} (hv : ∀ x, ‖v x‖=1) :
    ∀ x, ‖chartField d v x‖=1 := by
  intro x
  simpa only [chartField, LinearIsometryEquiv.norm_map] using hv ((directionChart d).symm x)

theorem coordinate_lipschitz {v : Plane → Plane} {K : ℝ≥0}
    (hv : LipschitzWith K v) (i : Fin 2) : LipschitzWith K (fun x => v x i) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  exact (PiLp.dist_apply_le (v x) (v y) i).trans (hv.dist_le_mul x y)

def chartDenominator (v : Plane → Plane) (x : Plane) : ℝ := max (1/2) (v x 0)

def rawChartSlope (v : Plane → Plane) (x : Plane) : ℝ :=
  v x 1 / chartDenominator v x

def clippedChartSlope (v : Plane → Plane) (x : Plane) : ℝ :=
  max (-(1/4)) (min (1/4) (rawChartSlope v x))

theorem ratio_dist_bound {a b c d : ℝ} (hb : 1/2≤b) (hd : 1/2≤d)
    (hc : |c|≤1) : |a/b-c/d|≤2*|a-c|+4*|b-d| := by
  have hb0 : 0<b := by linarith
  have hd0 : 0<d := by linarith
  calc
    |a/b-c/d| = |(a-c)/b+c*(d-b)/(b*d)| := by
      congr 1
      field_simp
      ring
    _ ≤ |(a-c)/b|+|c*(d-b)/(b*d)| := abs_add_le _ _
    _ = |a-c|/b+|c| *|b-d|/(b*d) := by
      rw [abs_div, abs_div, abs_mul, abs_mul, abs_sub_comm d b,
        abs_of_pos hb0, abs_of_pos hd0]
    _ ≤ 2*|a-c|+4*|b-d| := by
      apply add_le_add
      · apply (div_le_iff₀ hb0).mpr
        nlinarith [abs_nonneg (a-c)]
      · apply (div_le_iff₀ (mul_pos hb0 hd0)).mpr
        have hbd : 1/4≤b*d := by nlinarith
        nlinarith [abs_nonneg (b-d), mul_le_mul_of_nonneg_right hc (abs_nonneg (b-d))]

theorem rawChartSlope_lipschitz {v : Plane → Plane} {K : ℝ≥0}
    (hv : LipschitzWith K v) (hunit : ∀ x, ‖v x‖=1) :
    LipschitzWith (6*K) (rawChartSlope v) := by
  have hden := (coordinate_lipschitz hv 0).const_max (1/2)
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hc : |v y 1|≤1 := by
    simpa only [Real.norm_eq_abs, hunit y] using PiLp.norm_apply_le (v y) (1 : Fin 2)
  have hb := ratio_dist_bound (a := v x 1) (le_max_left (1/2) (v x 0))
    (le_max_left (1/2) (v y 0)) hc
  have h1 := (coordinate_lipschitz hv 1).dist_le_mul x y
  have h0 := hden.dist_le_mul x y
  simp only [Real.dist_eq] at h1 h0 ⊢
  change |rawChartSlope v x-rawChartSlope v y|≤_
  change |v x 1 / chartDenominator v x-v y 1 / chartDenominator v y|≤_ at hb
  simp only [chartDenominator] at hb ⊢
  simp only [NNReal.coe_mul, NNReal.coe_ofNat]
  dsimp [rawChartSlope, chartDenominator]
  nlinarith

theorem clippedChartSlope_lipschitz {v : Plane → Plane} {K : ℝ≥0}
    (hv : LipschitzWith K v) (hunit : ∀ x, ‖v x‖=1) :
    LipschitzWith (6*K) (clippedChartSlope v) :=
  ((rawChartSlope_lipschitz hv hunit).const_min (1/4)).const_max (-(1/4))

theorem clippedChartSlope_abs (v : Plane → Plane) (x : Plane) :
    |clippedChartSlope v x|≤1/4 := by
  rw [abs_le]
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

theorem chart_coordinates {d : Plane} (hd : ‖d‖=1) {q : Plane}
    (hq : dist q d<1/10) :
    9/10<(directionChart d q) 0 ∧ |(directionChart d q) 1|<1/10 := by
  have hc : dist (directionChart d q) horizontalUnit<1/10 := by
    rw [←directionChart_center d hd, LinearIsometryEquiv.dist_map]
    exact hq
  have h0 := (PiLp.dist_apply_le (directionChart d q) horizontalUnit (0 : Fin 2)).trans_lt hc
  have h1 := (PiLp.dist_apply_le (directionChart d q) horizontalUnit (1 : Fin 2)).trans_lt hc
  simp [horizontalUnit, Real.dist_eq] at h0 h1
  norm_num at h0 h1
  exact ⟨by linarith [(abs_lt.mp h0).1], h1⟩

theorem clippedChartSlope_eq_ratio {v : Plane → Plane} {x : Plane}
    (h0 : 9/10<v x 0) (h1 : |v x 1|<1/10) :
    clippedChartSlope v x=v x 1/v x 0 := by
  have hv : 0<v x 0 := by linarith
  have hr : |v x 1/v x 0|≤1/4 := by
    rw [abs_div, abs_of_pos hv, div_le_iff₀ hv]
    linarith
  simp only [clippedChartSlope,rawChartSlope,chartDenominator,
    max_eq_right (by linarith : (1:ℝ)/2≤v x 0),
    min_eq_right (abs_le.mp hr).2, max_eq_right (abs_le.mp hr).1]

theorem exists_finite_direction_charts :
    ∃ D : Finset Plane, (∀ d∈D, ‖d‖=1) ∧
      ∀ q : Plane, ‖q‖=1 → ∃ d∈D, dist q d<1/10 := by
  obtain ⟨s, hs, hfin, hcover⟩ :=
    (isCompact_sphere (0 : Plane) 1).finite_cover_balls (by norm_num : (0:ℝ)<1/10)
  classical
  refine ⟨hfin.toFinset, ?_, ?_⟩
  · intro d hd
    simpa only [Metric.mem_sphere, dist_zero_right] using hs (hfin.mem_toFinset.mp hd)
  · intro q hq
    have hm := hcover (show q∈Metric.sphere (0 : Plane) 1 by simpa using hq)
    simp only [Set.mem_iUnion, Metric.mem_ball] at hm
    obtain ⟨d, hd, hdist⟩ := hm
    exact ⟨d, hfin.mem_toFinset.mpr hd, hdist⟩

end LipschitzHilbert

end

end OAI
