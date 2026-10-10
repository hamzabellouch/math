import Mathlib
import OAI.Analysis.RieszRectifiability.Projections.NonemptyAffineProjection

namespace OAI

/-!
Orthogonal projection and distances to an affine plane control ambient distances.
The same estimate locates a chart from its planar coordinates and height bound.
-/

namespace RieszRectifiability

noncomputable section

open Metric Set

theorem dist_le_projection_add_plane_distances {d : ℕ}
    (S : AffineSubspace ℝ (Ambient d)) (hS : (S : Set (Ambient d)).Nonempty)
    (x c : Ambient d) :
    dist x c ≤ dist (S.direction.starProjection x) (S.direction.starProjection c) +
      infDist x (S : Set (Ambient d)) + infDist c (S : Set (Ambient d)) := by
  let : Nonempty S := hS.to_subtype
  have hn := normal_projection_bound_by_plane_distances S x c
  have ht := norm_add_le (S.direction.starProjection (x - c))
    ((S.directionᗮ : Submodule ℝ (Ambient d)).starProjection (x - c))
  rw [S.direction.starProjection_add_starProjection_orthogonal] at ht
  rw [map_sub, ← dist_eq_norm x c,
    ← dist_eq_norm (S.direction.starProjection x) (S.direction.starProjection c)] at ht
  calc
    dist x c ≤ dist (S.direction.starProjection x) (S.direction.starProjection c) +
        ‖(S.directionᗮ : Submodule ℝ (Ambient d)).starProjection (x - c)‖ := ht
    _ ≤ dist (S.direction.starProjection x) (S.direction.starProjection c) +
        (infDist x (S : Set (Ambient d)) + infDist c (S : Set (Ambient d))) :=
      add_le_add le_rfl hn
    _ = _ := by ring

theorem plane_chart_location_of_height {d : ℕ}
    (S : AffineSubspace ℝ (Ambient d)) (hS : (S : Set (Ambient d)).Nonempty)
    (c : Ambient d) (ρ B : ℝ)
    (g : closedBall (S.direction.orthogonalProjectionOnto c) ρ → Ambient d)
    (hcoordinates : ∀ u, S.direction.orthogonalProjectionOnto (g u) = u.val)
    (hheight : ∀ u, infDist (g u) (S : Set (Ambient d)) ≤ B) :
    ∀ u, dist (g u) c ≤ ρ + B + infDist c (S : Set (Ambient d)) := by
  intro u
  have hstar : S.direction.starProjection (g u) = (u.val : Ambient d) :=
    congrArg (fun v : S.direction => (v : Ambient d)) (hcoordinates u)
  have h := dist_le_projection_add_plane_distances S hS (g u) c
  rw [hstar] at h
  have hu : dist (u.val : Ambient d) (S.direction.starProjection c) ≤ ρ := u.property
  linarith [hheight u]

end

end RieszRectifiability

end OAI
