import Mathlib
import OAI.Analysis.RieszRectifiability.Nets.EuclideanBallNet
import OAI.Analysis.RieszRectifiability.Packing.AffinePlaneNormalFrame

namespace OAI

/-!
# Covering tubes around affine planes

Affine orthogonal projection is distance nonincreasing. Combining this estimate with
Euclidean ball nets gives finite covers of bounded tubes, with a cardinality estimate
in the dimension of the plane.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set EuclideanGeometry

theorem affine_projection_difference {d : ℕ}
    (S : AffineSubspace ℝ (Ambient d)) [Nonempty S] (x y : Ambient d) :
    (orthogonalProjection S x : Ambient d) - (orthogonalProjection S y : Ambient d) =
      S.direction.starProjection (x - y) := by
  rw [orthogonalProjection_apply', orthogonalProjection_apply']
  simp only [Submodule.coe_orthogonalProjectionOnto_apply, vsub_eq_sub, vadd_eq_add]
  rw [add_sub_add_right_eq_sub, ← map_sub, sub_sub_sub_cancel_right]

theorem affine_projection_dist_le {d : ℕ}
    (S : AffineSubspace ℝ (Ambient d)) [Nonempty S] (x y : Ambient d) :
    dist (orthogonalProjection S x : Ambient d) (orthogonalProjection S y : Ambient d) ≤ dist x y := by
  rw [dist_eq_norm, affine_projection_difference, dist_eq_norm]
  exact S.direction.norm_starProjection_apply_le (x - y)

theorem exists_affine_tube_ball_cover {k d : ℕ}
    (S : AffineSubspace ℝ (Ambient d)) (hS : IsAffineNPlane k S)
    (R δ : ℝ) (hR : 0 ≤ R) (hδ : 0 < δ) :
    ∃ c : Finset (Ambient d),
      (∀ x : Ambient d, ‖x‖ ≤ R → infDist x (S : Set (Ambient d)) < δ →
        ∃ y ∈ c, dist x y < 2 * δ) ∧
      (c.card : ℝ) * (δ / 2) ^ k ≤ (R + δ / 2) ^ k := by
  classical
  let : Nonempty S := hS.1.to_subtype
  let a : Ambient d := orthogonalProjection S (0 : Ambient d)
  have ha : a ∈ S := orthogonalProjection_mem (0 : Ambient d)
  obtain ⟨L, hL⟩ := exists_isometry_onto_subspace S.direction hS.2
  obtain ⟨s, _hs, hcover, hcard⟩ := exists_euclidean_ball_net (k := k) R δ hR hδ
  let f : Ambient k → Ambient d := fun t => a + L t
  have hf : Function.Injective f := by
    intro t t' h
    exact L.injective (add_left_cancel h)
  refine ⟨s.image f, ?_, ?_⟩
  · intro x hx hdist
    let p : Ambient d := orthogonalProjection S x
    have hp : p ∈ S := orthogonalProjection_mem x
    have hdir : p - a ∈ L.toLinearMap.range := by
      rw [hL]
      exact AffineSubspace.vsub_mem_direction hp ha
    obtain ⟨t, ht⟩ := hdir
    change L t = p - a at ht
    have hpt : a + L t = p := by rw [ht]; abel
    have htR : ‖t‖ ≤ R := by
      calc
        _ = ‖L t‖ := (L.norm_map t).symm
        _ = dist p a := by rw [ht, dist_eq_norm]
        _ ≤ dist x 0 := affine_projection_dist_le S x 0
        _ = ‖x‖ := dist_zero_right x
        _ ≤ R := hx
    obtain ⟨y, hy, hty⟩ := hcover t htR
    refine ⟨f y, Finset.mem_image.mpr ⟨y, hy, rfl⟩, ?_⟩
    have hpdist : dist p (f y) = dist t y := by
      change dist p (a + L y) = dist t y
      rw [← hpt, dist_add_left, L.isometry.dist_eq]
    have hxp : dist x p < δ := by
      simpa only [p, dist_orthogonalProjection_eq_infDist] using! hdist
    have htri := dist_triangle x p (f y)
    rw [hpdist] at htri
    linarith
  · rw [Finset.card_image_of_injective s hf]
    exact hcard

end

end RieszRectifiability

end OAI
