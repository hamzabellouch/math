import OAI.GroupTheory.PolycyclicRecognition.Geometry.RotationRepresentationFaithful
import OAI.GroupTheory.PolycyclicRecognition.Algebra.ChooseFaithfulMatrixRepresentation

namespace OAI

/-! # A faithful triangular representation of the rotational group -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold Matrix.Norms.Operator
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

theorem exists_faithful_rotation_triangular_representation :
    ∃ m : ℕ, 0 < m ∧
      ∃ j : CartanRealShadow T H →ₗ⁅ℝ⁆ Matrix (Fin m) (Fin m) ℝ,
        (Function.Injective j ∧ (∀ x, (j x).IsUpperTriangular) ∧
          (∀ x ∈ realShadowKernel T H, IsNilpotent (j x))) ∧
      ∃ ρ : F.SmoothRotationalModification hExp →* (Matrix (Fin m) (Fin m) ℝ)ˣ,
        Continuous ρ ∧ Function.Injective ρ ∧
        ∀ (x : T.kernelIdeal) (h : H),
          ρ (F.nilpotentFactorToRotation hExp (F.ExpN (F.N.equiv x)) *
            F.cartanFactorToRotation hExp (F.ExpD (F.D.equiv h))) =
            algebraExpUnit (j (cartanRealShadowEquiv T H x)) *
              algebraExpUnit (j (cartanRealShadowEquiv T H h)) := by
  refine exists_faithful_matrix_integration
    (fun _ j => Function.Injective j ∧ (∀ x, (j x).IsUpperTriangular) ∧
      (∀ x ∈ realShadowKernel T H, IsNilpotent (j x)))
    (fun x : T.kernelIdeal => cartanRealShadowEquiv T H x)
    (fun h : H => cartanRealShadowEquiv T H h)
    (fun x h => F.rotationExponentialProduct hExp (x,h))
    (exists_realShadow_triangularRepresentation T H) ?_ ?_
  · intro m j _
    exact F.exists_integrated_rotation_representation hExp j
  · intro m j hj ρ he
    exact F.rotationRepresentation_faithful hExp j hj.1 hj.2.1 ρ he

end ComplexWeightFactorModel
end PolycyclicRecognition

end

end OAI
