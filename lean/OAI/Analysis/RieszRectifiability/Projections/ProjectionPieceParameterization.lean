import Mathlib
import OAI.Analysis.RieszRectifiability.Projections.PairwisePlaneProjection
import OAI.Analysis.RieszRectifiability.Foundations.CoordinatePieceParameterization

namespace OAI

/-!
# Parameterizing pieces separated by projection

An orthogonal projection that separates points supplies Euclidean coordinates
for a Lipschitz ball parameterization. Pairwise approximating planes with
controlled angles provide a geometric criterion for this separation.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

theorem exists_ball_lipschitz_cover_of_projection {n d : ℕ}
    (E : Set (Ambient d)) (a : Ambient d) (r : ℝ) (hE : E ⊆ ball a r)
    (P : Submodule ℝ (Ambient d)) (hdim : Module.finrank ℝ P = n) (M : ℝ≥0)
    (hsep : ∀ x ∈ E, ∀ y ∈ E,
      dist x y ≤ (M : ℝ) * dist (P.starProjection x) (P.starProjection y)) :
    ∃ g : (ball (0 : Ambient n) r) → Ambient d,
      LipschitzWith (lipschitzExtensionConstant (Ambient d) * M) g ∧ E ⊆ range g := by
  obtain ⟨L, hL⟩ := exists_isometry_onto_subspace P hdim
  have hP (v : Ambient d) : P.starProjection v = L (L.toContinuousLinearMap.adjoint v) := by
    have heq := congrArg (fun T : Submodule ℝ (Ambient d) => T.starProjection v) hL
    exact heq.symm.trans (isometric_range_starProjection L v)
  let c (x : Ambient d) : Ambient n := L.toContinuousLinearMap.adjoint (x - a)
  have hball : ∀ x ∈ E, c x ∈ ball (0 : Ambient n) r := by
    intro x hx
    rw [mem_ball, dist_zero_right]
    calc
      _ = ‖L (c x)‖ := (L.norm_map _).symm
      _ = ‖P.starProjection (x - a)‖ := by rw [hP]
      _ ≤ ‖x - a‖ := P.norm_starProjection_apply_le _
      _ < r := by simpa only [mem_ball, dist_eq_norm] using! hE hx
  have hdist (x y : Ambient d) : dist (c x) (c y) = dist (P.starProjection x) (P.starProjection y) := by
    have hc : c x - c y = L.toContinuousLinearMap.adjoint (x - y) := by
      dsimp [c]
      rw [← map_sub, sub_sub_sub_cancel_right]
    rw [dist_eq_norm, ← L.norm_map, hc, ← hP, map_sub, ← dist_eq_norm]
  apply exists_ball_lipschitz_cover_of_coordinates E r c M hball
  intro x hx y hy
  rw [hdist]
  exact hsep x hx y hy

theorem exists_ball_lipschitz_cover_of_pairwise_planes {n d : ℕ}
    (E : Set (Ambient d)) (a : Ambient d) (r : ℝ) (hE : E ⊆ ball a r)
    (P : Submodule ℝ (Ambient d)) (hdim : Module.finrank ℝ P = n)
    (hfit : ∀ x ∈ E, ∀ y ∈ E, ∃ S : AffineSubspace ℝ (Ambient d),
      IsAffineNPlane n S ∧
        infDist x (S : Set (Ambient d)) ≤ (1 / 8) * dist x y ∧
        infDist y (S : Set (Ambient d)) ≤ (1 / 8) * dist x y ∧
        ∀ v ∈ S.direction,
          ‖(Pᗮ : Submodule ℝ (Ambient d)).starProjection v‖ ≤ (1 / 4) * ‖v‖) :
    ∃ g : (ball (0 : Ambient n) r) → Ambient d,
      LipschitzWith (lipschitzExtensionConstant (Ambient d) * 2) g ∧ E ⊆ range g := by
  apply exists_ball_lipschitz_cover_of_projection E a r hE P hdim 2
  intro x hx y hy
  obtain ⟨S, hS, hxS, hyS, hangle⟩ := hfit x hx y hy
  let : Nonempty S := hS.1.to_subtype
  exact projection_separates_of_pairwise_plane P S x y (1 / 8) (1 / 4)
    (by norm_num) (by norm_num) hxS hyS hangle

end

end RieszRectifiability

end OAI
