import OAI.MeasureTheory.Falconer.Geometry.ScaledDyadicPacking
import OAI.MeasureTheory.Falconer.Radial.RadialDensity
import Mathlib.Tactic.FieldSimp

namespace OAI

namespace PlanarFalconer
open Set Metric

 theorem normalized_vector_dist_le (u v : Plane) (hu : u ≠ 0) (hv : v ≠ 0) :
    dist (‖u‖⁻¹ • u) (‖v‖⁻¹ • v) ≤ 2*dist u v/‖u‖ := by
  have hu0 : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hv0 : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hid : ‖u‖⁻¹ • u - ‖v‖⁻¹ • v =
      ‖u‖⁻¹ • (u-v) + (‖u‖⁻¹-‖v‖⁻¹) • v := by
    rw [smul_sub, sub_smul]
    abel
  have hcoeff : |‖u‖⁻¹-‖v‖⁻¹| * ‖v‖ = |‖v‖-‖u‖|/‖u‖ := by
    rw [show ‖u‖⁻¹-‖v‖⁻¹ = (‖v‖-‖u‖)/(‖u‖*‖v‖) by
      field_simp [ne_of_gt hu0, ne_of_gt hv0],
      abs_div, abs_mul, abs_of_pos hu0, abs_of_pos hv0]
    field_simp [ne_of_gt hu0, ne_of_gt hv0]
  rw [dist_eq_norm, hid]
  calc
    _ ≤ ‖‖u‖⁻¹ • (u-v)‖ + ‖(‖u‖⁻¹-‖v‖⁻¹) • v‖ := norm_add_le _ _
    _ = ‖u-v‖/‖u‖ + |‖v‖-‖u‖|/‖u‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hu0), hcoeff]
      ring
    _ ≤ ‖u-v‖/‖u‖ + ‖u-v‖/‖u‖ := by
      apply add_le_add le_rfl
      apply div_le_div_of_nonneg_right _ hu0.le
      simpa only [norm_sub_rev] using abs_norm_sub_norm_le v u
    _ = _ := by rw [dist_eq_norm]; ring

 theorem endpoint_direction_dist_le {x y c d : Plane} (hxy : y ≠ x) (hcd : d ≠ c) :
    dist (sourceRadialUnit x y) (sourceRadialUnit c d) ≤
      2*(dist x c + dist y d)/dist x y := by
  change dist (sourceRadialVector x y) (sourceRadialVector c d) ≤ _
  simp only [sourceRadialVector, ite_eq_right hxy, ite_eq_right hcd]
  have hn := normalized_vector_dist_le (y-x) (d-c) (sub_ne_zero.mpr hxy) (sub_ne_zero.mpr hcd)
  have hd : dist (y-x) (d-c) ≤ dist x c + dist y d := by
    rw [dist_eq_norm, show (y-x)-(d-c) = (y-d)-(x-c) by abel]
    exact (norm_sub_le _ _).trans_eq (by rw [dist_eq_norm,dist_eq_norm]; ring)
  have he : ‖y-x‖ = dist x y := by rw [dist_eq_norm, norm_sub_rev]
  rw [he] at hn ⊢
  exact hn.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hd (by norm_num))
    (dist_nonneg))

 theorem dyadic_endpoint_direction_dist_le (P Q : DyadicSquare)
    (hP : 0 < P.side) (hQ : 0 < Q.side) {x y : Plane}
    (hx : x ∈ P.carrier) (hy : y ∈ Q.carrier) (hxy : y ≠ x)
    (hc : Q.center ≠ P.center) :
    dist (sourceRadialUnit x y) (sourceRadialUnit P.center Q.center) ≤
      4*(P.side+Q.side)/dist x y := by
  apply (endpoint_direction_dist_le hxy hc).trans
  have h1 := P.dist_le hP.le hx (P.center_mem hP)
  have h2 := Q.dist_le hQ.le hy (Q.center_mem hQ)
  apply div_le_div_of_nonneg_right _ dist_nonneg
  linarith

 theorem excluded_direction_separation {actual center dir : UnitCircle} {δ ε K : ℝ}
    (hmove : dist actual center ≤ ε) (hexcluded : K*δ ≤ dist center dir) :
    K*δ-ε ≤ dist actual dir := by
  have htri := dist_triangle center actual dir
  rw [dist_comm center actual] at htri
  linarith

end PlanarFalconer

end OAI
