import OAI.Geometry.SurfaceImmersion.Geometry.ConditionalMain
import OAI.Geometry.SurfaceImmersion.Whitney.WhitneySurfaceImmersion

namespace OAI

/-! Every compact smooth Riemannian surface, including nonorientable and
disconnected surfaces, admits a smooth isometric immersion into Euclidean
four-space. -/
noncomputable section
open Manifold
open scoped ContDiff
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M] [SecondCountableTopology M]

theorem smooth_isometric_immersion (g : SmoothMetric M) :
    ∃ F : M → Space, IsSmoothIsometricImmersion M g F :=
  smooth_isometric_immersion_conditional g PublishedInputs.whitneySurfaceInput

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
