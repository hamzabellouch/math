import Mathlib
import OAI.Analysis.RieszRectifiability.Nets.PointCellChains
import OAI.Analysis.RieszRectifiability.Projections.ProjectionPieceParameterization

namespace OAI

/-!
# Lipschitz charts from coherent cell fits

For each pair of points, a descendant at the separation scale supplies a nearby affine
plane with small angle to a fixed subspace. The resulting lower bound on projected
distances gives an inverse Lipschitz estimate and a ball parameterization of the piece.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

theorem projection_separates_of_coherent_cell_fits {n d : ℕ}
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points)
    (E : Set (Ambient d)) (hE : E ⊆ cleanSupportCell μ R hR k z)
    (P : Submodule ℝ (Ambient d))
    (hfit : ∀ i : SupportCellDescendant μ R hR k z,
      (E ∩ i.cell).Nonempty → ∃ S : AffineSubspace ℝ (Ambient d),
        IsAffineNPlane n S ∧
        (∀ w ∈ E ∩ ball i.center (1024 * i.radius), infDist w (S : Set (Ambient d)) ≤ i.radius) ∧
        ∀ v ∈ S.direction,
          ‖(Pᗮ : Submodule ℝ (Ambient d)).starProjection v‖ ≤ (1 / 4) * ‖v‖) :
    ∀ x ∈ E, ∀ y ∈ E, dist x y ≤ 2 * dist (P.starProjection x) (P.starProjection y) := by
  intro x hx y hy
  by_cases hxy : x = y
  · simp only [hxy, dist_self, mul_zero, le_refl]
  obtain ⟨i, hxi, hupper, _, hxball, hyball⟩ :=
    exists_pair_scale_support_descendant μ R hR k z x y (hE hx) (hE hy) hxy
  obtain ⟨S, hS, hnear, hangle⟩ := hfit i ⟨x, hx, hxi⟩
  let : Nonempty S := hS.1.to_subtype
  have hxs : infDist x (S : Set (Ambient d)) ≤ (1 / 8) * dist x y := by
    have h := hnear x ⟨hx, hxball⟩
    linarith
  have hys : infDist y (S : Set (Ambient d)) ≤ (1 / 8) * dist x y := by
    have h := hnear y ⟨hy, hyball⟩
    linarith
  exact projection_separates_of_pairwise_plane P S x y (1 / 8) (1 / 4)
    (by norm_num) (by norm_num) hxs hys hangle

theorem exists_ball_lipschitz_cover_of_coherent_cell_fits {n d : ℕ}
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points)
    (E : Set (Ambient d)) (hE : E ⊆ cleanSupportCell μ R hR k z)
    (a : Ambient d) (r : ℝ) (hball : E ⊆ ball a r)
    (P : Submodule ℝ (Ambient d)) (hdim : Module.finrank ℝ P = n)
    (hfit : ∀ i : SupportCellDescendant μ R hR k z,
      (E ∩ i.cell).Nonempty → ∃ S : AffineSubspace ℝ (Ambient d),
        IsAffineNPlane n S ∧
        (∀ w ∈ E ∩ ball i.center (1024 * i.radius), infDist w (S : Set (Ambient d)) ≤ i.radius) ∧
        ∀ v ∈ S.direction,
          ‖(Pᗮ : Submodule ℝ (Ambient d)).starProjection v‖ ≤ (1 / 4) * ‖v‖) :
    ∃ g : (ball (0 : Ambient n) r) → Ambient d,
      LipschitzWith (lipschitzExtensionConstant (Ambient d) * 2) g ∧ E ⊆ range g := by
  exact exists_ball_lipschitz_cover_of_projection E a r hball P hdim 2
    (projection_separates_of_coherent_cell_fits μ R hR k z E hE P hfit)

end

end RieszRectifiability

end OAI
