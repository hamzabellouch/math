import Mathlib

namespace OAI

noncomputable section
open Bundle Manifold
open scoped ContDiff

namespace ClosedSurfaceR4

abbrev Plane := EuclideanSpace ℝ (Fin 2)
abbrev Space := EuclideanSpace ℝ (Fin 4)
abbrev planeModel := 𝓘(ℝ, Plane)
abbrev spaceModel := 𝓘(ℝ, Space)

section

variable (M : Type*) [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [CompactSpace M]
  [ChartedSpace Plane M] [IsManifold planeModel ∞ M]

abbrev SmoothMetric :=
  Bundle.ContMDiffRiemannianMetric planeModel ∞ Plane
    (fun p : M => TangentSpace planeModel p)

def IsSmoothIsometricImmersion (g : SmoothMetric M) (F : M → Space) : Prop :=
  ContMDiff planeModel spaceModel ∞ F ∧
  ∀ (p : M) (v w : TangentSpace planeModel p),
    inner ℝ (mfderiv planeModel spaceModel F p v)
      (mfderiv planeModel spaceModel F p w) = g.inner p v w

end

namespace FiniteOrderSmoothing

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M] [SecondCountableTopology M]

/-- Every compact smooth Riemannian surface admits a smooth isometric immersion into Euclidean four-space. -/
theorem smooth_isometric_immersion (g : SmoothMetric M) :
    ∃ F : M → Space, IsSmoothIsometricImmersion M g F := by
  sorry

end FiniteOrderSmoothing
end ClosedSurfaceR4

end

end OAI
