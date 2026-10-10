import OAI.GroupTheory.PolycyclicRecognition.Geometry.RotationFactorParameter
import OAI.GroupTheory.PolycyclicRecognition.Geometry.RotationRepresentationIntegration
import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialParameterChart
import OAI.GroupTheory.PolycyclicRecognition.Geometry.ShadowExponentialCoordinates

namespace OAI

/-! # Concrete analytic representation coordinates for the rotational graph -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff
attribute [local instance 100] LieRing.ofAssociativeRing

variable {E G A : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ,E)) ⊤ G]
  [NormedRing A] [NormedAlgebra ℝ A] [FiniteDimensional ℝ A]
  {a : ℕ} {T : ComplexTriangularAdjoint (GroupLieAlgebra (𝓘(ℝ,E)) G) a}
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ,E)) G)} [H.IsCartanSubalgebra]
  {Exp : GroupLieAlgebra (𝓘(ℝ,E)) G → G}

namespace ComplexWeightFactorModel
variable (F : ComplexWeightFactorModel T H Exp) (hExp : IsGroupExponential Exp)
attribute [local instance] semidirectProductTopology

theorem exists_rotation_representedLocalChart
    (j : CartanRealShadow T H →ₗ⁅ℝ⁆ A) (hj : Function.Injective j)
    (ρ : F.SmoothRotationalModification hExp →* Aˣ)
    (he : ∀ (x : T.kernelIdeal) (h : H),
      ρ (F.nilpotentFactorToRotation hExp (F.ExpN (F.N.equiv x)) *
        F.cartanFactorToRotation hExp (F.ExpD (F.D.equiv h))) =
        algebraExpUnit (j (cartanRealShadowEquiv T H x)) *
          algebraExpUnit (j (cartanRealShadowEquiv T H h))) :
    Nonempty (RepresentedLocalChart (E := E) ρ) := by
  apply representedLocalChart_of_exponential_localization ρ (F.rotationFactorParameter hExp)
    (shadowKernelParameter T H j).toContinuousLinearMap
    (shadowCartanParameter T H j).toContinuousLinearMap
    (shadowParameters_injective T H j hj) _ (F.exists_rotationFactorParameter_chart hExp)
  intro v
  exact he (T.kernelComponent H v) (T.cartanComponent H v)

end ComplexWeightFactorModel
end PolycyclicRecognition

end

end OAI
