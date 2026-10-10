import Mathlib
import OAI.Analysis.RieszRectifiability.Projections.PairwisePlaneProjection

namespace OAI

/-!
# Comparing nearby plane directions

Distances to affine planes control normal projections of differences. Directional
projection bounds can then be composed through an intermediate linear subspace.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set EuclideanGeometry

theorem normal_projection_bound_by_plane_distances {d : ℕ}
    (W : AffineSubspace ℝ (Ambient d)) [Nonempty W] (x y : Ambient d) :
    ‖(W.directionᗮ : Submodule ℝ (Ambient d)).starProjection (x - y)‖ ≤
      infDist x (W : Set (Ambient d)) + infDist y (W : Set (Ambient d)) := by
  have hid : (x - y) - W.direction.starProjection (x - y) =
      (x - (orthogonalProjection W x : Ambient d)) -
        (y - (orthogonalProjection W y : Ambient d)) := by
    rw [← affine_projection_difference W x y]
    abel
  rw [W.direction.starProjection_orthogonal_val, hid]
  calc
    _ ≤ ‖x - (orthogonalProjection W x : Ambient d)‖ +
        ‖y - (orthogonalProjection W y : Ambient d)‖ := norm_sub_le _ _
    _ = _ := by
      rw [← dist_eq_norm, ← dist_eq_norm]
      exact congrArg₂ (· + ·) (dist_orthogonalProjection_eq_infDist W x)
        (dist_orthogonalProjection_eq_infDist W y)

theorem direction_normal_bound_of_local_plane_tube {d : ℕ}
    (S W : AffineSubspace ℝ (Ambient d)) [Nonempty W]
    (a : Ambient d) (ha : a ∈ S) (r η : ℝ) (hr : 0 < r)
    (htube : ∀ x ∈ S, x ∈ closedBall a r → infDist x (W : Set (Ambient d)) ≤ η * r) :
    ∀ v ∈ S.direction,
      ‖(W.directionᗮ : Submodule ℝ (Ambient d)).starProjection v‖ ≤ (2 * η) * ‖v‖ := by
  intro v hv
  by_cases hv0 : v = 0
  · simp only [hv0, map_zero, norm_zero, mul_zero, le_refl]
  have hvp : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  have hc : 0 < r / ‖v‖ := div_pos hr hvp
  let x := (r / ‖v‖) • v + a
  have hxs : x ∈ S := S.vadd_mem_of_mem_direction (S.direction.smul_mem (r / ‖v‖) hv) ha
  have hxa : dist x a = r := by
    change ‖(r / ‖v‖) • v + a - a‖ = r
    rw [add_sub_cancel_right, norm_smul, Real.norm_eq_abs, abs_of_pos hc, div_mul_cancel₀ _ hvp.ne']
  have hnear := htube x hxs (by rw [mem_closedBall, hxa])
  have hbase := htube a ha (mem_closedBall_self hr.le)
  have hn := normal_projection_bound_by_plane_distances W x a
  have hscaled : (r / ‖v‖) * ‖(W.directionᗮ : Submodule ℝ (Ambient d)).starProjection v‖ ≤
      2 * η * r := by
    have hxsub : x - a = (r / ‖v‖) • v := by dsimp [x]; abel
    rw [hxsub, map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hc] at hn
    linarith
  apply le_of_mul_le_mul_left (a := r) _ hr
  calc
    r * ‖(W.directionᗮ : Submodule ℝ (Ambient d)).starProjection v‖ =
        ((r / ‖v‖) * ‖(W.directionᗮ : Submodule ℝ (Ambient d)).starProjection v‖) * ‖v‖ := by
      field_simp [hvp.ne']
    _ ≤ (2 * η * r) * ‖v‖ := mul_le_mul_of_nonneg_right hscaled hvp.le
    _ = r * ((2 * η) * ‖v‖) := by ring

theorem compose_direction_normal_bounds {d : ℕ}
    (P T S : Submodule ℝ (Ambient d)) (α β : ℝ) (hα : 0 ≤ α)
    (hST : ∀ v ∈ S, ‖(Tᗮ : Submodule ℝ (Ambient d)).starProjection v‖ ≤ β * ‖v‖)
    (hTP : ∀ v ∈ T, ‖(Pᗮ : Submodule ℝ (Ambient d)).starProjection v‖ ≤ α * ‖v‖) :
    ∀ v ∈ S, ‖(Pᗮ : Submodule ℝ (Ambient d)).starProjection v‖ ≤ (α + β) * ‖v‖ := by
  intro v hv
  let Q := (Pᗮ : Submodule ℝ (Ambient d)).starProjection
  have hmem : T.starProjection v ∈ T := (T.orthogonalProjectionOnto v).property
  have hid : Q v = Q (v - T.starProjection v) + Q (T.starProjection v) := by
    rw [← map_add, sub_add_cancel]
  calc
    _ = ‖Q (v - T.starProjection v) + Q (T.starProjection v)‖ := by rw [← hid]
    _ ≤ ‖Q (v - T.starProjection v)‖ + ‖Q (T.starProjection v)‖ := norm_add_le _ _
    _ ≤ ‖v - T.starProjection v‖ + α * ‖T.starProjection v‖ :=
      add_le_add ((Pᗮ : Submodule ℝ (Ambient d)).norm_starProjection_apply_le _) (hTP _ hmem)
    _ = ‖(Tᗮ : Submodule ℝ (Ambient d)).starProjection v‖ + α * ‖T.starProjection v‖ := by
      rw [T.starProjection_orthogonal_val]
    _ ≤ β * ‖v‖ + α * ‖v‖ := add_le_add (hST v hv)
      (mul_le_mul_of_nonneg_left (T.norm_starProjection_apply_le v) hα)
    _ = _ := by ring

end

end RieszRectifiability

end OAI
