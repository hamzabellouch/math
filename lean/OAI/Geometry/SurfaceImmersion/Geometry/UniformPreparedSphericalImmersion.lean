import OAI.Geometry.SurfaceImmersion.Geometry.PreparedSphericalImmersion
import OAI.Geometry.SurfaceImmersion.Atlas.AtlasBackgroundLowerBound

namespace OAI

/-! Finite-point spherical preparation with all constants chosen before the
finite set, including domination of a fixed background metric. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology Manifold
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SphericalJets
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem uniform_prepared_spherical_immersion (g : SmoothMetric M) {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (hunit : ∀ p, ‖F p‖ = 1)
    (hImm : ∀ p, Function.Injective (mfderiv planeModel spaceModel F p)) :
    ∃ D c : ℝ, 0 ≤ D ∧ 0 < c ∧ ∀ (P : Finset M) (ε : ℝ), 0 < ε →
      ∃ (a : P → A.centers) (G : M → Space),
        (∀ p, A.weight (a p) p ≠ 0) ∧ ContMDiff planeModel spaceModel ∞ G ∧
        (∀ p, ‖G p‖ = 1) ∧
        (∀ p, Function.Injective (mfderiv planeModel spaceModel G p)) ∧
        A.WeightedBound 1 1 ε (G-F) ∧ A.WeightedBound 1 2 D G ∧
        (∀ p v, c*g.inner p v v ≤ inducedForm G p v v) ∧
        ∀ p : P, G p = F p ∧
          fderiv ℝ (G ∘ (chartAt Plane (a p : M)).symm) (chartAt Plane (a p : M) p) =
            fderiv ℝ (F ∘ (chartAt Plane (a p : M)).symm) (chartAt Plane (a p : M) p) ∧
          ∀ v w, sphericalSecondForm (G ∘ (chartAt Plane (a p : M)).symm)
            (chartAt Plane (a p : M) p) v w = 0 := by
  obtain ⟨D,hD,hprep⟩ := A.prepared_spherical_immersion hF hunit hImm
  obtain ⟨δ,c,hδ,hc,hlower⟩ := A.uniform_background_metric_lower_bound g hF hImm
  refine ⟨D,c,hD,hc,?_⟩
  intro P ε hε
  obtain ⟨a,G,ha,hG,hu,hI,hclose,hC,hflat⟩ := hprep P (min ε δ) (lt_min hε hδ)
  exact ⟨a,G,ha,hG,hu,hI,fun i => (hclose i).mono_const (min_le_left _ _),hC,
    hlower G hG (fun i => (hclose i).mono_const (min_le_right _ _)),hflat⟩

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
