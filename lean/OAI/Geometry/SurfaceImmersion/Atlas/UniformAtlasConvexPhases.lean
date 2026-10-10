import OAI.Geometry.SurfaceImmersion.Atlas.AtlasMetricJetFamily
import OAI.Geometry.SurfaceImmersion.Atlas.AtlasMetricReadGerms
import OAI.Geometry.SurfaceImmersion.Atlas.CenteredConvexPhase

namespace OAI

/-! Uniform strictly convex phases for the actual intermediate metrics.
The phase constants precede every choice of metric in the bounded family. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology Manifold
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SmallModes PhaseMean PhaseGeometry JetPolynomial.Perturbation
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem uniform_atlas_convex_phases (g : SmoothMetric M) {c C K : ℝ}
    (hc : 0 < c) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (houter : ∀ i p, p ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 p] (fun _ => 1)) :
    ∃ L r : ℝ, 0 < L ∧ 0 < r ∧
      ∀ h : SmoothMetric M, A.TensorWeightedBound 1 1 C h.inner →
        (∀ p v, c*g.inner p v v ≤ h.inner p v v) →
        ∀ (i : A.centers) (p : M), p ∈ tsupport (A.weight i) →
          ‖coordinateChart (i : M) p-coordinateChart (i : M) (i : M)‖ ≤ r →
          ∀ ell : SmallModes.Base, ‖ell‖ ≤ K → ∀ v : SmallModes.Base,
            (L/2)*(v.1^2+v.2^2) ≤ coordinateMetricHessian (coordinateMetric h (i : M))
              (centeredConvexPhase ell L (coordinateChart (i : M) (i : M)))
              (coordinateChart (i : M) p) v v := by
  obtain ⟨J,hJ,hdet,hmem⟩ := A.compact_metric_jet_family g hc hC
  obtain ⟨L,r,hL,hr,hess⟩ := compact_uniform_centered_convex_phases hJ hdet hK
  refine ⟨L,r,hL,hr,?_⟩
  intro h hb hlower i p hp hsmall ell hell v
  have hx : coordinateChart (i : M) p ∈
      (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) := by
    exact ⟨chart (i : M) p,⟨p,hp,rfl⟩,rfl⟩
  have hj := hmem h hb hlower i _ hx
  rw [A.tensorPlaneRead_metric_firstJet h i (A.weight_support i hp) (houter i p hp)] at hj
  exact hess (coordinateMetric h (i : M)) ell _ _ hell hsmall hj v

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
