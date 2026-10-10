import Mathlib
import OAI.Analysis.RieszRectifiability.Restart.ActiveProjectionDiskCoverage
import OAI.Analysis.RieszRectifiability.Projections.CoveredProjectionCharts

namespace OAI

/-!
# Initial affine-plane charts

Orthogonal coordinates parametrize each affine-plane disk by a 1-Lipschitz chart with
constant normal component and exact range. A distance estimate locates the chart near
an ambient center, with error given by that center's distance to the plane.
-/

namespace RieszRectifiability

noncomputable section

open Metric Set EuclideanGeometry
open scoped NNReal

theorem exists_affine_plane_disk_chart {d : ℕ}
    (S : AffineSubspace ℝ (Ambient d)) (hS : (S : Set (Ambient d)).Nonempty)
    (a : S.direction) (ρ : ℝ) :
    ∃ g : closedBall a ρ → Ambient d,
      LipschitzWith 1 g ∧
      LipschitzWith 0 (fun u => (S.directionᗮ : Submodule ℝ (Ambient d)).starProjection (g u)) ∧
      (∀ u, g u ∈ S ∧ S.direction.orthogonalProjectionOnto (g u) = u.val) ∧
      Set.range g = (S : Set (Ambient d)) ∩ S.direction.orthogonalProjectionOnto ⁻¹' closedBall a ρ := by
  let : Nonempty S := hS.to_subtype
  have hcover : closedBall a ρ ⊆ S.direction.orthogonalProjectionOnto '' (S : Set (Ambient d)) := by
    intro v _
    refine ⟨nonemptyAffineProjection S hS (v : Ambient d), ?_, ?_⟩
    · exact orthogonalProjection_mem (v : Ambient d)
    · rw [nonemptyAffineProjection_tangential]
      exact S.direction.orthogonalProjectionOnto_mem_subspace_eq_self v
  have hcone : ∀ x ∈ (S : Set (Ambient d)), ∀ y ∈ (S : Set (Ambient d)),
      ‖(S.directionᗮ : Submodule ℝ (Ambient d)).starProjection (x - y)‖ ≤
        ((0 : ℝ≥0) : ℝ) * dist (S.direction.starProjection x) (S.direction.starProjection y) := by
    intro x hx y hy
    have hv : x - y ∈ S.direction := AffineSubspace.vsub_mem_direction hx hy
    rw [S.direction.starProjection_orthogonal_val,
      S.direction.starProjection_eq_self_iff.mpr hv, sub_self, norm_zero, NNReal.coe_zero, zero_mul]
  simpa only [add_zero] using!
    exists_chart_on_covered_projection S.direction (S : Set (Ambient d)) 0 (closedBall a ρ) hcover hcone

theorem affine_plane_dist_le_projection_add_offset {d : ℕ}
    (S : AffineSubspace ℝ (Ambient d)) (hS : (S : Set (Ambient d)).Nonempty)
    (x c : Ambient d) (hx : x ∈ S) :
    dist x c ≤ dist (S.direction.starProjection x) (S.direction.starProjection c) +
      infDist c (S : Set (Ambient d)) := by
  let : Nonempty S := hS.to_subtype
  have hn := normal_projection_bound_by_plane_distances S x c
  rw [infDist_zero_of_mem hx, zero_add] at hn
  have ht := norm_add_le (S.direction.starProjection (x - c))
    ((S.directionᗮ : Submodule ℝ (Ambient d)).starProjection (x - c))
  rw [S.direction.starProjection_add_starProjection_orthogonal] at ht
  rw [map_sub, ← dist_eq_norm x c,
    ← dist_eq_norm (S.direction.starProjection x) (S.direction.starProjection c)] at ht
  exact ht.trans (add_le_add le_rfl hn)

theorem exists_located_affine_plane_disk_chart {d : ℕ}
    (S : AffineSubspace ℝ (Ambient d)) (hS : (S : Set (Ambient d)).Nonempty)
    (c : Ambient d) (ρ : ℝ) :
    ∃ g : closedBall (S.direction.orthogonalProjectionOnto c) ρ → Ambient d,
      LipschitzWith 1 g ∧
      LipschitzWith 0 (fun u => (S.directionᗮ : Submodule ℝ (Ambient d)).starProjection (g u)) ∧
      (∀ u, g u ∈ S ∧ S.direction.orthogonalProjectionOnto (g u) = u.val ∧
        dist (g u) c ≤ ρ + infDist c (S : Set (Ambient d))) ∧
      Set.range g = (S : Set (Ambient d)) ∩ S.direction.orthogonalProjectionOnto ⁻¹'
        closedBall (S.direction.orthogonalProjectionOnto c) ρ := by
  obtain ⟨g, hLip, hnLip, hcoords, hrange⟩ :=
    exists_affine_plane_disk_chart S hS (S.direction.orthogonalProjectionOnto c) ρ
  refine ⟨g, hLip, hnLip, ?_, hrange⟩
  intro u
  refine ⟨(hcoords u).1, (hcoords u).2, ?_⟩
  have hstar : S.direction.starProjection (g u) = (u.val : Ambient d) :=
    congrArg (fun v : S.direction => (v : Ambient d)) (hcoords u).2
  have h := affine_plane_dist_le_projection_add_offset S hS (g u) c (hcoords u).1
  rw [hstar] at h
  have hu : dist (u.val : Ambient d) (S.direction.starProjection c) ≤ ρ := u.property
  exact h.trans (add_le_add hu le_rfl)

end

end RieszRectifiability

end OAI
