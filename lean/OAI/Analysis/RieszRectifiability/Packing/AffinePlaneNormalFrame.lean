import Mathlib
import OAI.Analysis.RieszRectifiability.Packing.OrthogonalNormalFrame
import OAI.Analysis.RieszRectifiability.Kernel.NormalizedNormalCoordinates
import OAI.Analysis.RieszRectifiability.Kernel.LeastSquaredExcess

namespace OAI

/-!
# Normal coordinates for affine planes

Isometric tangent and normal frames express affine orthogonal projection and distance
to a plane in Euclidean coordinates. The frame construction chooses the point of the
plane nearest the origin as its base point.
-/

namespace RieszRectifiability

noncomputable section

open Metric Set EuclideanGeometry

theorem exists_euclidean_isometric_embedding {n d : ℕ} (hnd : n ≤ d) :
    Nonempty (Ambient n →ₗᵢ[ℝ] Ambient d) := by
  have hdim : n ≤ Module.finrank ℝ (Ambient d) := by
    simpa only [finrank_euclideanSpace_fin] using! hnd
  obtain ⟨v, hv⟩ := exists_linearIndependent_of_le_finrank hdim
  have hspan : Module.finrank ℝ (Submodule.span ℝ (range v)) = n := by
    simpa only [Fintype.card_fin] using! finrank_span_eq_card hv
  obtain ⟨L, _hL⟩ := exists_isometry_onto_subspace (Submodule.span ℝ (range v)) hspan
  exact ⟨L⟩

theorem affine_plane_projection_of_frame {n d : ℕ}
    (S : AffineSubspace ℝ (Ambient d)) [Nonempty S] (a : Ambient d) (ha : a ∈ S)
    (L : Ambient n →ₗᵢ[ℝ] Ambient d) (hL : L.toLinearMap.range = S.direction)
    (x : Ambient d) :
    (orthogonalProjection S x : Ambient d) = tangentPlaneProjection a L x := by
  have hproj : S.direction.starProjection (x - a) =
      L (L.toContinuousLinearMap.adjoint (x - a)) := by
    have heq := congrArg (fun T : Submodule ℝ (Ambient d) => T.starProjection (x - a)) hL
    exact heq.symm.trans (isometric_range_starProjection L (x - a))
  calc
    _ = S.direction.starProjection (x - a) + a := by
      simpa only [vsub_eq_sub, vadd_eq_add, Submodule.coe_orthogonalProjectionOnto_apply]
        using! orthogonalProjection_apply_mem S ha (p := x)
    _ = _ := by rw [hproj]; exact add_comm _ _

theorem affine_plane_distance_normal_frame {n q d : ℕ}
    (S : AffineSubspace ℝ (Ambient d)) [Nonempty S] (a : Ambient d) (ha : a ∈ S)
    (L : Ambient n →ₗᵢ[ℝ] Ambient d) (hL : L.toLinearMap.range = S.direction)
    (N : Ambient q →ₗᵢ[ℝ] Ambient d)
    (hsplit : ∀ y, L (L.toContinuousLinearMap.adjoint y) +
      N (N.toContinuousLinearMap.adjoint y) = y) (x : Ambient d) :
    infDist x (S : Set (Ambient d)) = ‖N.toContinuousLinearMap.adjoint (x - a)‖ := by
  rw [← dist_orthogonalProjection_eq_infDist S x, affine_plane_projection_of_frame S a ha L hL]
  simpa only [normalizedNormalHeight, inv_one, one_smul, one_mul]
    using! physical_projection_distance_eq a L N hsplit 1 zero_lt_one x

theorem exists_affine_plane_normal_frame {n d : ℕ}
    (S : AffineSubspace ℝ (Ambient d)) (hS : IsAffineNPlane n S) :
    ∃ a : Ambient d, a ∈ S ∧ ‖a‖ = infDist (0 : Ambient d) (S : Set (Ambient d)) ∧
      ∃ L : Ambient n →ₗᵢ[ℝ] Ambient d, L.toLinearMap.range = S.direction ∧
      ∃ N : Ambient (d - n) →ₗᵢ[ℝ] Ambient d,
        (∀ y, L.toContinuousLinearMap.adjoint (N y) = 0) ∧
        (∀ y, L (L.toContinuousLinearMap.adjoint y) +
          N (N.toContinuousLinearMap.adjoint y) = y) ∧
        ∀ x, infDist x (S : Set (Ambient d)) = ‖N.toContinuousLinearMap.adjoint (x - a)‖ := by
  let : Nonempty S := hS.1.to_subtype
  let a : Ambient d := orthogonalProjection S (0 : Ambient d)
  have ha : a ∈ S := orthogonalProjection_mem (0 : Ambient d)
  have hnorm : ‖a‖ = infDist (0 : Ambient d) (S : Set (Ambient d)) := by
    simpa only [dist_zero_left] using! dist_orthogonalProjection_eq_infDist S (0 : Ambient d)
  obtain ⟨L, hL⟩ := exists_isometry_onto_subspace S.direction hS.2
  obtain ⟨N, horth, hsplit⟩ := exists_complete_normal_frame L
  exact ⟨a, ha, hnorm, L, hL, N, horth, hsplit,
    affine_plane_distance_normal_frame S a ha L hL N hsplit⟩

end

end RieszRectifiability

end OAI
