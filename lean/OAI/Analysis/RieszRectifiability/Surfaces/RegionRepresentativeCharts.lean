import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.RegionRepresentativeGeometry

namespace OAI

/-!
# Lipschitz charts for region representatives

Good cells at the scale of each pair provide affine-plane tube and angle bounds.
These bounds make projection onto the reference plane separate region representatives
with inverse Lipschitz constant two. A Lipschitz extension then covers the representatives
by the image of a ball in the Euclidean space of the plane's dimension.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal

theorem projection_separates_region_representatives {n d : ℕ}
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop)
    (hroot : ∀ i : SupportCellDescendant μ R hR k z, i.depth = 0 → Good i)
    (P : Submodule ℝ (Ambient d))
    (hfit : ∀ i : SupportCellDescendant μ R hR k z, Good i →
      ∃ S : AffineSubspace ℝ (Ambient d), IsAffineNPlane n S ∧
        (∀ w ∈ ball i.center (1024 * i.radius), w ∈ μ.support →
          infDist w (S : Set (Ambient d)) ≤ i.radius / 16384) ∧
        ∀ v ∈ S.direction,
          ‖(Pᗮ : Submodule ℝ (Ambient d)).starProjection v‖ ≤ (1 / 4 : ℝ) * ‖v‖) :
    ∀ x ∈ cellRegionRepresentatives μ R hR k z Good,
    ∀ y ∈ cellRegionRepresentatives μ R hR k z Good,
      dist x y ≤ 2 * dist (P.starProjection x) (P.starProjection y) := by
  intro x hx y hy
  by_cases hxy : x = y
  · simp only [hxy, dist_self, mul_zero, le_refl]
  obtain ⟨q, hgood, _, hupper, _, hxball, hyball⟩ :=
    exists_good_pair_cell_for_representatives μ R hR k z Good hroot x y hx hy hxy
  obtain ⟨S, hS, htube, hangle⟩ := hfit q hgood
  let : Nonempty S := hS.1.to_subtype
  have hxμ := supportLatticeCell_subset_support μ R hR k z
    (cellRegionRepresentatives_subset_top μ R hR k z Good hx).1
  have hyμ := supportLatticeCell_subset_support μ R hR k z
    (cellRegionRepresentatives_subset_top μ R hR k z Good hy).1
  have hxS : infDist x (S : Set (Ambient d)) ≤ (1 / 32 : ℝ) * dist x y := by
    have h := htube x hxball hxμ
    linarith
  have hyS : infDist y (S : Set (Ambient d)) ≤ (1 / 32 : ℝ) * dist x y := by
    have h := htube y hyball hyμ
    linarith
  exact projection_separates_of_pairwise_plane P S x y (1 / 32) (1 / 4)
    (by norm_num) (by norm_num) hxS hyS hangle

theorem exists_ball_lipschitz_cover_of_region_representatives {n d : ℕ}
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop)
    (hroot : ∀ i : SupportCellDescendant μ R hR k z, i.depth = 0 → Good i)
    (P : Submodule ℝ (Ambient d)) (hdim : Module.finrank ℝ P = n)
    (hfit : ∀ i : SupportCellDescendant μ R hR k z, Good i →
      ∃ S : AffineSubspace ℝ (Ambient d), IsAffineNPlane n S ∧
        (∀ w ∈ ball i.center (1024 * i.radius), w ∈ μ.support →
          infDist w (S : Set (Ambient d)) ≤ i.radius / 16384) ∧
        ∀ v ∈ S.direction,
          ‖(Pᗮ : Submodule ℝ (Ambient d)).starProjection v‖ ≤ (1 / 4 : ℝ) * ‖v‖) :
    ∃ g : (ball (0 : Ambient n) (3 * latticeRadius R k)) → Ambient d,
      LipschitzWith (lipschitzExtensionConstant (Ambient d) * 2) g ∧
        cellRegionRepresentatives μ R hR k z Good ⊆ range g := by
  have hball : cellRegionRepresentatives μ R hR k z Good ⊆
      ball (z : Ambient d) (3 * latticeRadius R k) := by
    intro x hx
    have hb := (supportLatticeCell_bounds μ R hR k z).2
      (cellRegionRepresentatives_subset_top μ R hR k z Good hx).1
    change dist x (z : Ambient d) ≤ 2 * latticeRadius R k at hb
    rw [mem_ball]
    have hr := latticeRadius_pos R hR k
    linarith
  exact exists_ball_lipschitz_cover_of_projection _ _ _ hball P hdim 2
    (projection_separates_region_representatives μ R hR k z Good hroot P hfit)

end

end RieszRectifiability

end OAI
