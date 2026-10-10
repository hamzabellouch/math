import Mathlib
import OAI.Analysis.RieszRectifiability.Restart.ActiveProjectionLocalComparison
import OAI.Analysis.RieszRectifiability.Projections.ProjectionPerturbationCone
import OAI.Analysis.RieszRectifiability.Projections.ProjectionConeGraph

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem activeProjectionError_small_parameters (d : ℕ) (ε : ℝ) (hε : 0 < ε)
    (hsmall : activeProjectionError d ε ≤ 1 / 4) :
    0 ≤ activeProjectionError d ε ∧ ε ≤ 1 / 1024 := by
  have hp : 0 ≤ (1048576 * (9 : ℝ) ^ d) * ε := by positivity
  constructor
  · unfold activeProjectionError
    positivity
  · unfold activeProjectionError at hsmall
    nlinarith

theorem activeLevelProjectionMap_local_graph {n d : ℕ}
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop) (t : ℕ)
    (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
    (hS : ∀ i, IsAffineNPlane n (S i)) (ε : ℝ) (hε : 0 < ε)
    (hsmall : activeProjectionError d ε ≤ 1 / 4)
    (hfit : ∀ i ∈ activeLevelIndex μ R hR k z Good t,
      bilateralPlaneError μ i.center (1024 * i.radius) (S i) < ε)
    (q : SupportCellDescendant μ R hR k z)
    (hq : q ∈ activeLevelIndex μ R hR k z Good t)
    (E : Set (Ambient d))
    (hlocal : E ⊆ closedBall q.center (3 * latticeRadius R (k + t)))
    (hinput : ∀ x ∈ E, ∀ y ∈ E,
      dist x y ≤ 2 * dist ((S q).direction.starProjection x) ((S q).direction.starProjection y)) :
    let f := activeLevelProjectionMap μ R hR k z Good t S hS
    let P := (S q).direction
    Set.InjOn f E ∧
      LipschitzOnWith (Real.toNNReal (1 + activeProjectionError d ε)) f E ∧
      ∃ g : (P.starProjection '' (f '' E)) → Ambient d,
        LipschitzWith (Real.toNNReal (4 * activeProjectionError d ε)) g ∧
        (∀ u, g u ∈ (Pᗮ : Submodule ℝ (Ambient d))) ∧
        f '' E = Set.range (fun u : P.starProjection '' (f '' E) => u.val + g u) := by
  let f := activeLevelProjectionMap μ R hR k z Good t S hS
  let P := (S q).direction
  let η := activeProjectionError d ε
  obtain ⟨hη, hεsmall⟩ := activeProjectionError_small_parameters d ε hε hsmall
  have herr : ∀ x ∈ E, ∀ y ∈ E,
      ‖(f x - f y) - P.starProjection (x - y)‖ ≤ η * dist x y := by
    intro x hx y hy
    exact activeLevelProjectionMap_reference_increment μ R hR k z Good t S hS
      ε hε hεsmall hfit q hq x y (hlocal hx) (hlocal hy)
  have hforward : LipschitzOnWith (Real.toNNReal (1 + η)) f E := by
    apply LipschitzOnWith.of_dist_le'
    intro x hx y hy
    have hv : ‖x - y‖ ≤ 2 * ‖P.starProjection (x - y)‖ := by
      simpa only [map_sub, dist_eq_norm] using! hinput x hx y hy
    exact (projection_perturbation_vector_bounds P (x - y) (f x - f y) η
      hη hsmall hv (herr x hx y hy)).2.2.1
  refine ⟨projection_perturbation_injOn P E f η hη hsmall hinput herr, hforward, ?_⟩
  apply exists_normal_graph_of_projection_cone P (f '' E) (4 * η) (mul_nonneg (by norm_num) hη)
  exact projection_perturbation_image_cone P E f η hη hsmall hinput herr

end

end RieszRectifiability

end OAI
