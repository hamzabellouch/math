import Mathlib
import OAI.Analysis.RieszRectifiability.Surfaces.PerturbedBallCoverage
import OAI.Analysis.RieszRectifiability.Projections.PlaneChangeProjectedMap

namespace OAI

/-!
# Disk coverage after changing the reference plane

A graph with small normal Lipschitz constant projects onto a smaller disk in a
nearby plane. Coverage follows from the Lipschitz perturbation bound for its
transferred parameter map.
-/

namespace RieszRectifiability

noncomputable section

open Metric Set
open scoped NNReal

theorem graph_covers_changed_plane_disk {d : ℕ}
    (P Q : Submodule ℝ (Ambient d)) (a : P) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (g : closedBall a ρ → Ambient d) (L α : ℝ≥0) (hsmall : L + α < 1)
    (hcoordinates : ∀ v, P.orthogonalProjectionOnto (g v) = v.val)
    (hnormal : LipschitzWith L
      (fun v => (Pᗮ : Submodule ℝ (Ambient d)).starProjection (g v)))
    (hop : ‖P.starProjection - Q.starProjection‖ ≤ (α : ℝ)) :
    let b := Q.orthogonalProjectionOnto (g ⟨a, mem_closedBall_self hρ⟩)
    closedBall b (ρ - ((L : ℝ) + (α : ℝ)) * ρ) ⊆ Q.orthogonalProjectionOnto '' Set.range g := by
  let a₀ : closedBall a ρ := ⟨a, mem_closedBall_self hρ⟩
  let b := Q.orthogonalProjectionOnto (g a₀)
  let b₀ : closedBall b ρ := ⟨b, mem_closedBall_self hρ⟩
  let f := planeChangedParameterMap P Q a b ρ g
  have herror : LipschitzWith (L + α) (fun v : closedBall b ρ => f v - v.val) :=
    planeChangedParameterMap_error_lipschitz P Q a b ρ g L α hcoordinates hnormal hop
  have hzero : f b₀ - b₀.val = 0 := by
    change Q.orthogonalProjectionOnto (g (projectionDiskLift P Q a b ρ b₀)) - b = 0
    rw [projectionDiskLift_center P Q a b ρ hρ]
    exact sub_self _
  have hdisp : ∀ v : closedBall b ρ, dist (f v) v.val ≤ ((L : ℝ) + (α : ℝ)) * ρ := by
    intro v
    have h := herror.dist_le_mul v b₀
    rw [hzero, dist_zero_right, NNReal.coe_add] at h
    have hd : dist v b₀ ≤ ρ := v.property
    rw [dist_eq_norm]
    exact h.trans (mul_le_mul_of_nonneg_left hd (add_nonneg L.coe_nonneg α.coe_nonneg))
  have hcover := closedBall_covered_by_lipschitz_perturbation b ρ
    (((L : ℝ) + (α : ℝ)) * ρ) hρ (L + α) hsmall f hdisp herror
  change closedBall b (ρ - ((L : ℝ) + (α : ℝ)) * ρ) ⊆ Q.orthogonalProjectionOnto '' Set.range g
  intro y hy
  obtain ⟨v, hv⟩ := hcover hy
  exact ⟨g (projectionDiskLift P Q a b ρ v),
    ⟨projectionDiskLift P Q a b ρ v, rfl⟩, hv⟩

end

end RieszRectifiability

end OAI
