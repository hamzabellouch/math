import OAI.GroupTheory.PolycyclicRecognition.Geometry.RotationFactorProduct
import OAI.GroupTheory.PolycyclicRecognition.Algebra.ComplexFactorLocalChart
import OAI.GroupTheory.PolycyclicRecognition.Geometry.ManifoldLocalParameter
import OAI.GroupTheory.PolycyclicRecognition.Algebra.HomeomorphicParameter

namespace OAI

/-! # Local coordinates for the rotational graph from the original factors -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff

variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ,E)) ⊤ G]
  {a : ℕ} {T : ComplexTriangularAdjoint (GroupLieAlgebra (𝓘(ℝ,E)) G) a}
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ,E)) G)} [H.IsCartanSubalgebra]
  {Exp : GroupLieAlgebra (𝓘(ℝ,E)) G → G}

namespace ComplexWeightFactorModel
variable (F : ComplexWeightFactorModel T H Exp) (hExp : IsGroupExponential Exp)
attribute [local instance] semidirectProductTopology

def rotationFactorParameter (v : E) : F.SmoothRotationalModification hExp :=
  F.nilpotentFactorToRotation hExp (F.ExpN (F.kernelParameter v)) *
    F.cartanFactorToRotation hExp (F.ExpD (F.cartanParameter v))

theorem rotationFactorParameter_coordinates (v : E) :
    F.smoothRotationalModificationHomeomorph hExp (F.rotationFactorParameter hExp v) =
      F.factorParameter v := F.rotationFactorProduct_coordinates hExp _ _

theorem rotationFactorParameter_zero : F.rotationFactorParameter hExp 0 = 1 :=
  parameter_zero_of_coordinates (F.smoothRotationalModificationHomeomorph hExp) rfl
    (F.rotationFactorParameter hExp) F.factorParameter
    (F.rotationFactorParameter_coordinates hExp) F.factorParameter_zero

theorem exists_rotationFactorParameter_chart :
    ∃ p : OpenPartialHomeomorph E (F.SmoothRotationalModification hExp),
      (0 : E) ∈ p.source ∧ p 0 = 1 ∧
        ∀ v ∈ p.source, p v = F.rotationFactorParameter hExp v := by
  apply exists_parameter_of_coordinate_homeomorph
    (F.smoothRotationalModificationHomeomorph hExp) rfl
    (F.rotationFactorParameter hExp) F.factorParameter
    (F.rotationFactorParameter_coordinates hExp) F.factorParameter_zero
  exact exists_manifold_local_parameter (d := ContinuousLinearEquiv.refl ℝ E)
    (F.contMDiff_factorParameter hExp) (F.hasMFDerivAt_factorParameter hExp)

end ComplexWeightFactorModel
end PolycyclicRecognition

end

end OAI
