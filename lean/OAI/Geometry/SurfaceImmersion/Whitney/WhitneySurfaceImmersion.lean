import OAI.Geometry.SurfaceImmersion.Whitney.FiniteCrosscapCancellation
import OAI.Geometry.SurfaceImmersion.Geometry.PublishedInputs

namespace OAI

/-! The exact surface specialization of Whitney (1944), Theorem 8,
discharged by finite generic crosscap preparation and supported cancellation. -/
noncomputable section
open Manifold
open scoped ContDiff
namespace ClosedSurfaceR4.PublishedInputs
variable {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [CompactSpace M] [ChartedSpace Plane M] [IsManifold 𝓘(ℝ,Plane) ∞ M]

theorem whitneySurfaceInput : WhitneySurfaceInput M := by
  obtain ⟨f,hf,hI⟩ := FiniteOrderSmoothing.smooth_three_space_immersion (M := M)
  exact ⟨f,hf.of_le (by simp),hI⟩

end ClosedSurfaceR4.PublishedInputs

end

end OAI
