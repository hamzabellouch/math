import Mathlib
import OAI.Analysis.RieszRectifiability.Restart.ActiveProjectionLocalComparison

namespace OAI

/-!
# Surface bounds for active-level projections

Height bounds control the displacement of the active-level projection map on a
surface. Local comparison with a reference affine plane also bounds the distance
of the projected image from that plane at the current lattice scale.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set EuclideanGeometry

variable {n d : ℕ} (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
  (z : (supportLatticeNets μ R hR k).points)
  (Good : SupportCellDescendant μ R hR k z → Prop) (t : ℕ)
  (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
  (hS : ∀ i, IsAffineNPlane n (S i))

theorem activeLevelProjectionMap_surface_displacement
    (A : Set (Ambient d)) (B : ℝ) (hB : 0 ≤ B)
    (hheight : ∀ i ∈ activeLevelIndex μ R hR k z Good t, ∀ x ∈ A,
      dist x i.center < 4 * latticeRadius R (k + t) →
        infDist x (S i : Set (Ambient d)) ≤ B) :
    ∀ x ∈ A, dist (activeLevelProjectionMap μ R hR k z Good t S hS x) x ≤ B := by
  intro x hx
  apply finiteProjectionAverage_dist_self_le _ _ _ x B hB
    (fun i _ => activeLevelWeight_nonneg μ R hR k z Good t i x)
    (activeLevelWeight_sum_le_one μ R hR k z Good t x)
  intro i hi hn
  rw [nonemptyAffineProjection_dist_self]
  exact hheight i hi x hx ((activeLevelWeight_ne_zero_iff μ R hR k z Good t i x).mp hn)

theorem activeLevelProjectionMap_image_plane_height
    (ε : ℝ) (hε : 0 < ε) (hεsmall : ε ≤ 1 / 1024)
    (hfit : ∀ i ∈ activeLevelIndex μ R hR k z Good t,
      bilateralPlaneError μ i.center (1024 * i.radius) (S i) < ε)
    (q : SupportCellDescendant μ R hR k z)
    (hq : q ∈ activeLevelIndex μ R hR k z Good t)
    (E : Set (Ambient d))
    (hE : E ⊆ closedBall q.center (3 * latticeRadius R (k + t))) :
    ∀ y ∈ (activeLevelProjectionMap μ R hR k z Good t S hS) '' E,
      infDist y (S q : Set (Ambient d)) ≤ (262144 * ε) * latticeRadius R (k + t) := by
  let : Nonempty (S q) := (hS q).1.to_subtype
  rintro y ⟨x, hx, rfl⟩
  have hp : nonemptyAffineProjection (S q) (hS q).1 x ∈ S q :=
    orthogonalProjection_mem x
  exact (infDist_le_dist_of_mem hp).trans
    (activeLevelProjectionMap_reference_displacement μ R hR k z Good t S hS
      ε hε hεsmall hfit q hq x (hE hx))

end

end RieszRectifiability

end OAI
