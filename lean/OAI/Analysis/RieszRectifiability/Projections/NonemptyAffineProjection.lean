import Mathlib
import OAI.Analysis.RieszRectifiability.Flatness.LocalPlaneDirectionComparison

namespace OAI

/-!
# Affine projection with an explicit nonemptiness witness

This projection takes the plane's nonemptiness as an argument rather than a typeclass
assumption. Its displacement is the distance to the plane, and the map is 1-Lipschitz.
-/

namespace RieszRectifiability

noncomputable section

open Metric Set EuclideanGeometry

def nonemptyAffineProjection {d : ℕ} (S : AffineSubspace ℝ (Ambient d))
    (hS : (S : Set (Ambient d)).Nonempty) : Ambient d → Ambient d :=
  letI : Nonempty S := hS.to_subtype
  fun x => (orthogonalProjection S x : Ambient d)

theorem nonemptyAffineProjection_dist_self {d : ℕ}
    (S : AffineSubspace ℝ (Ambient d)) (hS : (S : Set (Ambient d)).Nonempty)
    (x : Ambient d) :
    dist (nonemptyAffineProjection S hS x) x = infDist x (S : Set (Ambient d)) := by
  let : Nonempty S := hS.to_subtype
  change dist (orthogonalProjection S x : Ambient d) x = _
  rw [dist_comm, dist_orthogonalProjection_eq_infDist]

theorem nonemptyAffineProjection_lipschitz {d : ℕ}
    (S : AffineSubspace ℝ (Ambient d)) (hS : (S : Set (Ambient d)).Nonempty) :
    LipschitzWith 1 (nonemptyAffineProjection S hS) := by
  let : Nonempty S := hS.to_subtype
  apply LipschitzWith.mk_one
  intro x y
  change dist (orthogonalProjection S x : Ambient d) (orthogonalProjection S y : Ambient d) ≤ _
  rw [dist_eq_norm, affine_projection_difference S x y]
  exact S.direction.norm_starProjection_apply_le (x - y)

end

end RieszRectifiability

end OAI
