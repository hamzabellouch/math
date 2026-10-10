import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

namespace OAI

/-!
# Recovering measurable orthogonal projections from distances

Polarization expresses every scalar coordinate of an orthogonal
projection using four distances to the subspace. This avoids an assumed
measurable choice of bases. It will be applied to the actual component
velocity spaces after their distance functions have been constructed.
-/

noncomputable section
open MeasureTheory
open scoped InnerProductSpace

namespace DukePrimeDegree

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma infDist_eq_norm_sub_starProjection (W : Submodule ℝ E)
    [W.HasOrthogonalProjection] (v : E) :
    Metric.infDist v (W : Set E) = ‖v - W.starProjection v‖ := by
  rw [Metric.infDist_eq_iInf, W.starProjection_minimal]
  congr 1
  funext w
  exact dist_eq_norm v w

lemma norm_starProjection_sq_eq (W : Submodule ℝ E)
    [W.HasOrthogonalProjection] (v : E) :
    ‖W.starProjection v‖ ^ 2 = ‖v‖ ^ 2 - Metric.infDist v (W : Set E) ^ 2 := by
  have hp := W.norm_sq_eq_add_norm_sq_starProjection v
  rw [Submodule.starProjection_orthogonal', sub_apply,
    one_apply_eq_self] at hp
  rw [infDist_eq_norm_sub_starProjection]
  linarith

/-- A coordinate of the projection is determined by the squared
projection norms at the sum and difference of two fixed vectors. -/
theorem inner_starProjection_from_distances (W : Submodule ℝ E)
    [W.HasOrthogonalProjection] (v w : E) :
    ⟪W.starProjection v, w⟫_ℝ =
      ((‖v + w‖ ^ 2 - Metric.infDist (v + w) (W : Set E) ^ 2) -
        (‖v - w‖ ^ 2 - Metric.infDist (v - w) (W : Set E) ^ 2)) / 4 := by
  have hproj : W.starProjection (W.starProjection v) = W.starProjection v :=
    W.starProjection_eq_self_iff.mpr (W.starProjection_apply_mem v)
  have hinner : ⟪W.starProjection v, W.starProjection w⟫_ℝ =
      ⟪W.starProjection v, w⟫_ℝ := by
    simpa only [hproj] using
      (W.inner_starProjection_left_eq_right (W.starProjection v) w).symm
  have hp := norm_add_sq_real (W.starProjection v) (W.starProjection w)
  have hm := norm_sub_sq_real (W.starProjection v) (W.starProjection w)
  rw [← map_add, norm_starProjection_sq_eq] at hp
  rw [← map_sub, norm_starProjection_sq_eq] at hm
  rw [hinner] at hp hm
  linarith

theorem measurable_inner_starProjection_of_distances
    {Z : Type*} [MeasurableSpace Z]
    (W : Z → Submodule ℝ E) [∀ z, (W z).HasOrthogonalProjection]
    (hd : ∀ v : E, Measurable (fun z => Metric.infDist v (W z : Set E)))
    (v w : E) : Measurable (fun z => ⟪(W z).starProjection v, w⟫_ℝ) := by
  simp_rw [inner_starProjection_from_distances]
  exact ((measurable_const.sub ((hd (v + w)).pow_const 2)).sub
    (measurable_const.sub ((hd (v - w)).pow_const 2))).div_const 4

end DukePrimeDegree

end

end OAI
