import Mathlib

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4

abbrev Plane := EuclideanSpace ℝ (Fin 2)
abbrev Space := EuclideanSpace ℝ (Fin 4)
abbrev planeModel := 𝓘(ℝ, Plane)
abbrev spaceModel := 𝓘(ℝ, Space)

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



end ClosedSurfaceR4

end

end OAI
