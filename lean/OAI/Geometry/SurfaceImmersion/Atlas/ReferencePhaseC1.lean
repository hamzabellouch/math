import OAI.Geometry.SurfaceImmersion.Geometry.ReferencePerturbationStability
import OAI.Geometry.SurfaceImmersion.Atlas.PhaseCovectorFamily

namespace OAI

/-! A fixed first-jet budget for every phase in the reference parameter balls. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace ReferenceCircularAtlas
variable {A : SmoothingAtlas M} {gref g : SmoothMetric M} {c C : ℝ}
  (d : ReferenceCircularAtlas A gref g c C)

theorem perturbed_phase_C1_bound : ∃ D : ℝ, 1 ≤ D ∧
    ∀ ell : d.B.centers → Fin 3 → SmallModes.Base,
      (∀ i j, ‖ell i j-(d.P i).ξ j‖ ≤ 1) →
      ∀ (i : d.B.centers) (a : d.B.centers × Fin 3) p,
      p ∈ tsupport (d.B.weight i) →
        ‖d.B.phaseCovectorRead i (d.perturbedPhases ell a) (chart (i : M) p)‖ ≤ D ∧
        ‖fderiv ℝ (d.B.phaseCovectorRead i (d.perturbedPhases ell a)) (chart (i : M) p)‖ ≤ D := by
  classical
  choose D hD hbound using fun k : d.B.centers × (d.B.centers × Fin 3) =>
    d.B.circular_covector_parameter_bound k.2.1 k.1 (d.L k.2.1)
      (isCompact_closedBall ((d.P k.2.1).ξ k.2.2) 1)
  let E := 1+∑ k, D k
  have hsum := Finset.sum_nonneg (s := Finset.univ) (fun k _ => zero_le_one.trans (hD k))
  refine ⟨E,by dsimp only [E]; linarith,?_⟩
  intro ell hell i a p hp
  have he : ell a.1 a.2 ∈ Metric.closedBall ((d.P a.1).ξ a.2) 1 := by
    simpa only [Metric.mem_closedBall,dist_eq_norm] using hell a.1 a.2
  have h := hbound (i,a) (ell a.1 a.2) he (chart (i : M) p) ⟨p,hp,rfl⟩
  have hle : D (i,a) ≤ E := by
    have hh := Finset.single_le_sum (fun k _ => zero_le_one.trans (hD k)) (Finset.mem_univ (i,a))
    dsimp only [E]; linarith
  exact ⟨h.1.trans hle,h.2.trans hle⟩

end ReferenceCircularAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
