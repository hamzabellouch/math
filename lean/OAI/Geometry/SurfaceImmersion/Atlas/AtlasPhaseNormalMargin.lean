import OAI.Geometry.SurfaceImmersion.Atlas.PhaseNormalTripleMargin
import OAI.Geometry.SurfaceImmersion.Primitive.AtlasPrimitiveNormal

namespace OAI

/-! Uniform phase-chart normal margins on a fixed smoothing-atlas patch. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial RealModes SurfaceVelocityFamily.Loop
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem phase_normal_margin (i : A.centers)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    (hcover : (A.chartWeightCompact i : Set JetPolynomial.Base) ⊆ e.source) :
    ∃ D : ℝ, 0 < D ∧ ∀ (V : M → Space), ContMDiff planeModel spaceModel ∞ V →
      ∀ x ∈ (A.chartWeightCompact i : Set JetPolynomial.Base), ∀ c : ℝ, 0 < c →
        (let J := primitiveNormalTriple (A.vectorChartRead i V ∘ e.symm) (e x)
         NormalFrame.gramDet (J 0) (J 1) ≠ 0 ∧ c < ‖realNormalPart (J 0) (J 1) (J 2)‖) →
        Function.Injective (fderiv ℝ (spaceCoordinates ∘ A.vectorPlaneRead i V)
          (planeCoordinateIsometry x)) ∧
        c/D < ‖realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i V)
          (planeCoordinateIsometry x)‖ := by
  obtain ⟨D,hD,hd⟩ := compact_phase_normalTriple_margin e he hi
    (A.chartWeightCompact i).isCompact hcover
  refine ⟨D,hD,?_⟩
  intro V hV x hx c hc hn
  have hh := hd (A.vectorChartRead i V) (A.vectorChartRead_smooth i hV) x hx c hc hn
  have heq : spaceCoordinates ∘ A.vectorChartRead i V ∘ planeCoordinateIsometry.symm =
      spaceCoordinates ∘ A.vectorPlaneRead i V := rfl
  rwa [heq] at hh

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
