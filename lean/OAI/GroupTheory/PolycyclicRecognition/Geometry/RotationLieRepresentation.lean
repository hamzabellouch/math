import OAI.GroupTheory.PolycyclicRecognition.Geometry.ActualRotationLieAlgebra
import OAI.GroupTheory.PolycyclicRecognition.Geometry.RealShadowRepresentationTransport

namespace OAI

/-! # A faithful real triangular representation of the actual graph Lie algebra -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff Matrix.Norms.Operator
attribute [local instance 100] LieRing.ofAssociativeRing

variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ,E)) ⊤ G]
  {a : ℕ} {T : ComplexTriangularAdjoint (GroupLieAlgebra (𝓘(ℝ,E)) G) a}
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ,E)) G)} [H.IsCartanSubalgebra]
  {Exp : GroupLieAlgebra (𝓘(ℝ,E)) G → G}

namespace ComplexWeightFactorModel
variable (F : ComplexWeightFactorModel T H Exp) (hExp : IsGroupExponential Exp)
attribute [local instance] semidirectProductTopology
local instance rotationRepresentationChartedSpace :
    ChartedSpace E (F.SmoothRotationalModification hExp) :=
  F.smoothRotationalModificationChartedSpace hExp
local instance rotationRepresentationLieGroup :
    LieGroup (𝓘(ℝ,E)) ∞ (F.SmoothRotationalModification hExp) :=
  F.smoothRotationalModificationLieGroup hExp
local instance rotationRepresentationLieOrderThree :
    LieGroup (𝓘(ℝ,E)) (minSmoothness ℝ 3) (F.SmoothRotationalModification hExp) :=
  LieGroup.of_le (n := ∞) (by simp)

theorem exists_rotation_triangularLieRepresentation :
    ∃ m : ℕ, 0 < m ∧
      ∃ j : GroupLieAlgebra (𝓘(ℝ,E)) (F.SmoothRotationalModification hExp) →ₗ⁅ℝ⁆
          Matrix (Fin m) (Fin m) ℝ,
        Function.Injective j ∧ (∀ x, (j x).IsUpperTriangular) ∧
        ∀ x, F.smoothRotationalModificationLieEquiv hExp x ∈ realShadowKernel T H →
          IsNilpotent (j x) :=
  realShadow_triangularRepresentation_pullback T H (F.smoothRotationalModificationLieEquiv hExp)

end ComplexWeightFactorModel
end PolycyclicRecognition

end

end OAI
