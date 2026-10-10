import OAI.Geometry.SurfaceImmersion.Geometry.C1ImmersionApproximation
import OAI.Geometry.SurfaceImmersion.Geometry.PublishedInputs
import OAI.Geometry.SurfaceImmersion.Atlas.SphericalMetricPhaseData

namespace OAI

/-! Starting geometry from the precise published C1 surface-immersion input.
The upgrade to a smooth immersion is proved by finite-atlas convolution. -/
noncomputable section
open Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing

variable {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [CompactSpace M] [ChartedSpace Plane M] [IsManifold planeModel ∞ M]

/-- Whitney (1944), Theorem 8 supplies only the C1 immersion. Its smoothing
is carried out here without adding a further published-input hypothesis. -/
theorem smooth_three_space_immersion_of_whitney
    (hW : PublishedInputs.WhitneySurfaceInput M) :
    ∃ f : M → PublishedInputs.ThreeSpace,
      ContMDiff planeModel 𝓘(ℝ,PublishedInputs.ThreeSpace) ∞ f ∧
      ∀ p, Function.Injective (mfderiv planeModel 𝓘(ℝ,PublishedInputs.ThreeSpace) f p) := by
  obtain ⟨f,hf,hI⟩ := hW
  obtain ⟨A⟩ := exists_smoothingAtlas (M := M)
  exact A.smooth_immersion_of_C1 hf hI

/-- The cited Whitney input yields a smooth spherical immersion together
with the actual finite phase data used by the metric correction. -/
theorem metricPhaseData_of_whitney (g : SmoothMetric M)
    (hW : PublishedInputs.WhitneySurfaceInput M) :
    ∃ G : M → Space, ContMDiff planeModel spaceModel ∞ G ∧
      (∀ p, ‖G p‖ = 1) ∧
      (∀ p, Function.Injective (mfderiv planeModel spaceModel G p)) ∧
      Nonempty (MetricGoodPhaseData g G) := by
  obtain ⟨f,hf,hI⟩ := smooth_three_space_immersion_of_whitney hW
  exact metricPhaseData_of_three_space_immersion g hf hI

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
