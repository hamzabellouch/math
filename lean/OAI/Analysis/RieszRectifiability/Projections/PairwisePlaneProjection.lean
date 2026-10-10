import Mathlib
import OAI.Analysis.RieszRectifiability.Flatness.AffineTubeCover

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set EuclideanGeometry

theorem contraction_bound_of_pairwise_plane {d : ℕ}
    (Q : Ambient d →L[ℝ] Ambient d) (S : AffineSubspace ℝ (Ambient d)) [Nonempty S]
    (x y : Ambient d) (ε α : ℝ) (hα : 0 ≤ α)
    (hQ : ∀ v : Ambient d, ‖Q v‖ ≤ ‖v‖)
    (hx : infDist x (S : Set (Ambient d)) ≤ ε * dist x y)
    (hy : infDist y (S : Set (Ambient d)) ≤ ε * dist x y)
    (hangle : ∀ v ∈ S.direction, ‖Q v‖ ≤ α * ‖v‖) :
    ‖Q (x - y)‖ ≤ (2 * ε + α) * dist x y := by
  let sx : Ambient d := orthogonalProjection S x
  let sy : Ambient d := orthogonalProjection S y
  have hsx : sx ∈ S := orthogonalProjection_mem x
  have hsy : sy ∈ S := orthogonalProjection_mem y
  have hw : ‖sx - sy‖ ≤ dist x y := by
    simpa only [dist_eq_norm] using! affine_projection_dist_le S x y
  have he : ‖(x - y) - (sx - sy)‖ ≤ 2 * ε * dist x y := by
    have hid : (x - y) - (sx - sy) = (x - sx) - (y - sy) := by abel
    calc
      _ = ‖(x - sx) - (y - sy)‖ := by rw [hid]
      _ ≤ ‖x - sx‖ + ‖y - sy‖ := norm_sub_le _ _
      _ = infDist x (S : Set (Ambient d)) + infDist y (S : Set (Ambient d)) := by
        rw [← dist_eq_norm, ← dist_eq_norm]
        exact congrArg₂ (· + ·) (dist_orthogonalProjection_eq_infDist S x)
          (dist_orthogonalProjection_eq_infDist S y)
      _ ≤ _ := by linarith
  have hdir : sx - sy ∈ S.direction := AffineSubspace.vsub_mem_direction hsx hsy
  have hid : Q (x - y) =
      Q ((x - y) - (sx - sy)) + Q (sx - sy) := by
    rw [← map_add, sub_add_cancel]
  calc
    _ = ‖Q ((x - y) - (sx - sy)) + Q (sx - sy)‖ := by rw [hid]
    _ ≤ ‖Q ((x - y) - (sx - sy))‖ + ‖Q (sx - sy)‖ := norm_add_le _ _
    _ ≤ ‖(x - y) - (sx - sy)‖ + α * ‖sx - sy‖ :=
      add_le_add (hQ _) (hangle _ hdir)
    _ ≤ 2 * ε * dist x y + α * dist x y :=
      add_le_add he (mul_le_mul_of_nonneg_left hw hα)
    _ = _ := by ring

theorem normal_projection_bound_of_pairwise_plane {d : ℕ}
    (P : Submodule ℝ (Ambient d)) (S : AffineSubspace ℝ (Ambient d)) [Nonempty S]
    (x y : Ambient d) (ε α : ℝ) (hα : 0 ≤ α)
    (hx : infDist x (S : Set (Ambient d)) ≤ ε * dist x y)
    (hy : infDist y (S : Set (Ambient d)) ≤ ε * dist x y)
    (hangle : ∀ v ∈ S.direction, ‖(Pᗮ : Submodule ℝ (Ambient d)).starProjection v‖ ≤ α * ‖v‖) :
    ‖(Pᗮ : Submodule ℝ (Ambient d)).starProjection (x - y)‖ ≤ (2 * ε + α) * dist x y := by
  exact contraction_bound_of_pairwise_plane (Pᗮ : Submodule ℝ (Ambient d)).starProjection S x y ε α hα
    (fun v => Submodule.norm_starProjection_apply_le (Pᗮ : Submodule ℝ (Ambient d)) v) hx hy hangle

theorem projection_separates_of_pairwise_plane {d : ℕ}
    (P : Submodule ℝ (Ambient d)) (S : AffineSubspace ℝ (Ambient d)) [Nonempty S]
    (x y : Ambient d) (ε α : ℝ) (hα : 0 ≤ α) (hsmall : 2 * ε + α ≤ 1 / 2)
    (hx : infDist x (S : Set (Ambient d)) ≤ ε * dist x y)
    (hy : infDist y (S : Set (Ambient d)) ≤ ε * dist x y)
    (hangle : ∀ v ∈ S.direction, ‖(Pᗮ : Submodule ℝ (Ambient d)).starProjection v‖ ≤ α * ‖v‖) :
    dist x y ≤ 2 * dist (P.starProjection x) (P.starProjection y) := by
  have hn := normal_projection_bound_of_pairwise_plane P S x y ε α hα hx hy hangle
  have hnhalf : ‖(Pᗮ : Submodule ℝ (Ambient d)).starProjection (x - y)‖ ≤ dist x y / 2 := by
    have hm := mul_le_mul_of_nonneg_right hsmall (show 0 ≤ dist x y from dist_nonneg)
    linarith
  have htri : dist x y ≤ ‖P.starProjection (x - y)‖ + ‖(Pᗮ : Submodule ℝ (Ambient d)).starProjection (x - y)‖ := by
    calc
      _ = ‖P.starProjection (x - y) + (Pᗮ : Submodule ℝ (Ambient d)).starProjection (x - y)‖ := by
        rw [P.starProjection_add_starProjection_orthogonal, dist_eq_norm]
      _ ≤ _ := norm_add_le _ _
  have hproj : dist (P.starProjection x) (P.starProjection y) = ‖P.starProjection (x - y)‖ := by
    rw [dist_eq_norm, map_sub]
  rw [hproj]
  linarith

end

end RieszRectifiability

end OAI
