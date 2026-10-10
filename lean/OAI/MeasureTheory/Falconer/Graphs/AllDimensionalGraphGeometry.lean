import OAI.MeasureTheory.Falconer.Estimates.AllDimensions
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace OAI

/-!
# Geometry of the retained graph in arbitrary dimension

The graph tests use orthogonal distance to a line and one scalar longitudinal
constraint. Each longitudinal constraint is in the unknown endpoint's own
cap direction. In particular these bounds do not divide by the angle between
the two endpoint directions.
-/

namespace Falconer

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Perpendicular displacement from the line in a unit direction. -/
def perpendicularPart (w v : E) : E := v - inner ℝ w v • w

theorem perpendicularPart_sub (w u v : E) :
    perpendicularPart w (u-v) = perpendicularPart w u - perpendicularPart w v := by
  simp only [perpendicularPart, inner_sub_right, sub_smul]
  abel

/-- Orthogonal projection is a contraction. -/
theorem norm_perpendicularPart_le {w : E} (hw : ‖w‖ = 1) (v : E) :
    ‖perpendicularPart w v‖ ≤ ‖v‖ := by
  have hn := norm_sub_sq_real v (inner ℝ w v • w)
  rw [real_inner_smul_right, real_inner_comm v w, norm_smul, hw,
    mul_one, Real.norm_eq_abs, sq_abs] at hn
  change ‖v - inner ℝ w v • w‖ ≤ ‖v‖
  rw [real_inner_comm v w]
  nlinarith [norm_nonneg (v - inner ℝ v w • w), norm_nonneg v, sq_nonneg (inner ℝ v w)]

/-- Moving a unit direction changes the perpendicular test by at most twice
its angular displacement times the size of the tested vector. -/
theorem perpendicularPart_direction_error {w z : E} (hw : ‖w‖ = 1) (hz : ‖z‖ = 1)
    (v : E) :
    ‖perpendicularPart w v - perpendicularPart z v‖ ≤ 2 * ‖w-z‖ * ‖v‖ := by
  have he : perpendicularPart w v - perpendicularPart z v =
      inner ℝ z v • (z-w) + inner ℝ (z-w) v • w := by
    simp only [perpendicularPart, inner_sub_left, sub_smul, smul_sub]
    abel
  rw [he]
  calc
    _ ≤ ‖inner ℝ z v • (z-w)‖ + ‖inner ℝ (z-w) v • w‖ := norm_add_le _ _
    _ = |inner ℝ z v| * ‖z-w‖ + |inner ℝ (z-w) v| := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, hw, mul_one]
    _ ≤ (‖z‖ * ‖v‖) * ‖z-w‖ + (‖z-w‖ * ‖v‖) := by
      exact add_le_add (mul_le_mul_of_nonneg_right (abs_real_inner_le_norm z v)
        (norm_nonneg _)) (abs_real_inner_le_norm (z-w) v)
    _ = _ := by rw [hz, one_mul, norm_sub_rev z w]; ring

/-- The error in a graph perpendicular test from both point and cap
replacement is controlled uniformly in the dimension. -/
theorem perpendicularPart_test_error {w z : E} (hw : ‖w‖ = 1) (hz : ‖z‖ = 1)
    (u v : E) :
    ‖perpendicularPart w u - perpendicularPart z v‖ ≤
      ‖u-v‖ + 2 * ‖w-z‖ * ‖v‖ := by
  calc
    _ ≤ ‖perpendicularPart w u - perpendicularPart w v‖ +
        ‖perpendicularPart w v - perpendicularPart z v‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ ‖u-v‖ + 2 * ‖w-z‖ * ‖v‖ := by
      rw [← perpendicularPart_sub]
      exact add_le_add (norm_perpendicularPart_le hw _) (perpendicularPart_direction_error hw hz v)

/-- Scalar phase error under point and cap replacement. -/
theorem longitudinal_test_error {w z : E} (hw : ‖w‖ = 1) (u v : E) :
    |inner ℝ w u - inner ℝ z v| ≤ ‖u-v‖ + ‖w-z‖ * ‖v‖ := by
  have he : inner ℝ w u - inner ℝ z v =
      inner ℝ w (u-v) + inner ℝ (w-z) v := by
    simp only [inner_sub_left, inner_sub_right]
    ring
  rw [he]
  calc
    _ ≤ |inner ℝ w (u-v)| + |inner ℝ (w-z) v| := abs_add_le _ _
    _ ≤ ‖w‖ * ‖u-v‖ + ‖w-z‖ * ‖v‖ :=
      add_le_add (abs_real_inner_le_norm _ _) (abs_real_inner_le_norm _ _)
    _ = _ := by rw [hw, one_mul]

/-- A perpendicular tube and a longitudinal interval together confine the
unknown point to a ball, regardless of any other direction in the graph. -/
theorem norm_le_longitudinal_add_perpendicular {w : E} (hw : ‖w‖ = 1) (v : E) :
    ‖v‖ ≤ |inner ℝ w v| + ‖perpendicularPart w v‖ := by
  have he : v = inner ℝ w v • w + perpendicularPart w v := by
    dsimp [perpendicularPart]
    abel
  calc
    ‖v‖ = ‖inner ℝ w v • w + perpendicularPart w v‖ := congrArg norm he
    _ ≤ ‖inner ℝ w v • w‖ + ‖perpendicularPart w v‖ := norm_add_le _ _
    _ = _ := by rw [norm_smul, Real.norm_eq_abs, hw, mul_one]

/-- Difference of two points satisfying the same scalar interval and the same
perpendicular tube belongs to a ball of the expected radius. -/
theorem two_test_diameter {w : E} (hw : ‖w‖ = 1) {u v : E} {a b : ℝ}
    (hlong : |inner ℝ w u - inner ℝ w v| ≤ a)
    (hperp : ‖perpendicularPart w u - perpendicularPart w v‖ ≤ b) :
    ‖u-v‖ ≤ a+b := by
  calc
    ‖u-v‖ ≤ |inner ℝ w (u-v)| + ‖perpendicularPart w (u-v)‖ :=
      norm_le_longitudinal_add_perpendicular hw _
    _ = |inner ℝ w u - inner ℝ w v| +
        ‖perpendicularPart w u - perpendicularPart w v‖ := by
      rw [inner_sub_right, perpendicularPart_sub]
    _ ≤ a+b := add_le_add hlong hperp

/-- When each point lies in a tube of radius τ and its scalar coordinate in
an interval of half-width τ, the full candidate diameter is at most 4τ. -/
theorem retained_candidates_diameter {w : E} (hw : ‖w‖ = 1) {u v : E} {c τ : ℝ}
    (hu : |inner ℝ w u - c| ≤ τ) (hv : |inner ℝ w v - c| ≤ τ)
    (hpu : ‖perpendicularPart w u‖ ≤ τ) (hpv : ‖perpendicularPart w v‖ ≤ τ) :
    ‖u-v‖ ≤ 4*τ := by
  have hlong : |inner ℝ w u - inner ℝ w v| ≤ 2*τ := by
    calc
      _ = |(inner ℝ w u-c) - (inner ℝ w v-c)| := by congr 1; ring
      _ ≤ |inner ℝ w u-c| + |inner ℝ w v-c| := abs_sub _ _
      _ ≤ 2*τ := by linarith
  have hperp : ‖perpendicularPart w u - perpendicularPart w v‖ ≤ 2*τ :=
    (norm_sub_le _ _).trans (by linarith)
  exact (two_test_diameter hw hlong hperp).trans_eq (by ring)

/-- Two centers retained in one cap lie in a slightly wider tube in any
nearby witness direction. This is the geometric input to the parallel test. -/
theorem witness_tube_bound {w w₀ : E} (hw : ‖w‖ = 1) (hw₀ : ‖w₀‖ = 1)
    {u v z : E} {τ δ L : ℝ} (hδ : 0 ≤ δ)
    (hu : ‖perpendicularPart w₀ (u-z)‖ ≤ τ)
    (hv : ‖perpendicularPart w₀ (v-z)‖ ≤ τ)
    (hclose : ‖w-w₀‖ ≤ δ) (hsize : ‖u-v‖ ≤ L) :
    ‖perpendicularPart w (u-v)‖ ≤ 2*τ + 2*δ*L := by
  have he : (u-z) - (v-z) = u-v := by abel
  have hbase : ‖perpendicularPart w₀ (u-v)‖ ≤ 2*τ := by
    rw [← he, perpendicularPart_sub]
    exact (norm_sub_le _ _).trans (by linarith)
  have herror := perpendicularPart_direction_error hw hw₀ (u-v)
  have hg : 2 * ‖w-w₀‖ * ‖u-v‖ ≤ 2*δ*L := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left hclose (by norm_num)) hsize
      (norm_nonneg _) (mul_nonneg (by norm_num) hδ)
  have ht := norm_sub_le_norm_sub_add_norm_sub
    (perpendicularPart w (u-v)) (perpendicularPart w₀ (u-v)) 0
  simp only [sub_zero] at ht
  linarith

end Falconer

end OAI
