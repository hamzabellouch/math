import OAI.GroupTheory.PolycyclicRecognition.Geometry.RotationRepresentationRelations
import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialRepresentationDescent
import OAI.GroupTheory.PolycyclicRecognition.Algebra.NilpotentContinuousRepresentation

namespace OAI

/-! # Integration of the real-shadow algebra on the actual rotational graph -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff
attribute [local instance 100] LieRing.ofAssociativeRing

variable {E G A : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ,E)) ⊤ G]
  [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] [FiniteDimensional ℝ A]
  {a : ℕ} {T : ComplexTriangularAdjoint (GroupLieAlgebra (𝓘(ℝ,E)) G) a}
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ,E)) G)} [H.IsCartanSubalgebra]
  {Exp : GroupLieAlgebra (𝓘(ℝ,E)) G → G}

namespace ComplexWeightFactorModel
variable (F : ComplexWeightFactorModel T H Exp) (hExp : IsGroupExponential Exp)
attribute [local instance] semidirectProductTopology

theorem exists_integrated_rotation_representation (j : CartanRealShadow T H →ₗ⁅ℝ⁆ A) :
    ∃ ρ : F.SmoothRotationalModification hExp →* Aˣ, Continuous ρ ∧
      ∀ (x : T.kernelIdeal) (h : H),
        ρ (F.nilpotentFactorToRotation hExp (F.ExpN (F.N.equiv x)) *
          F.cartanFactorToRotation hExp (F.ExpD (F.D.equiv h))) =
          algebraExpUnit (j (cartanRealShadowEquiv T H x)) *
            algebraExpUnit (j (cartanRealShadowEquiv T H h)) := by
  let : IsTopologicalGroup Aˣ := topologicalGroup_of_lieGroup (𝓘(ℝ,A)) ⊤
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ,E)) ⊤
  let jN : T.kernelIdeal →ₗ⁅ℝ⁆ A := j.comp ((realShadowKernel T H).incl.comp
    (realShadowKernelEquiv T H).toLieHom)
  let jD : H →ₗ⁅ℝ⁆ A := j.comp (realShadowCartanHom T H)
  refine exists_representation_with_factor_coordinates
    (F.rotationFactorAction hExp) (F.nilpotentFactorToRotation hExp)
    (F.cartanFactorToRotation hExp)
    (F.closedEmbedding_nilpotentFactorToRotation hExp).continuous
    (F.closedEmbedding_cartanFactorToRotation hExp).continuous
    (fun d => MonoidHom.ext (fun n => F.rotationFactorAction_conjugation hExp d n))
    (F.rotationFactorProduct_surjective hExp) (F.rotationFactorProduct_open hExp)
    (fun x : T.kernelIdeal => F.ExpN (F.N.equiv x))
    (fun h : H => F.ExpD (F.D.equiv h))
    (fun x => algebraExpUnit (j (cartanRealShadowEquiv T H x)))
    (fun h => algebraExpUnit (j (cartanRealShadowEquiv T H h))) ?_ ?_ ?_
  · exact F.N.exists_continuous_algebra_representation
      T.kernelIdeal_nilpotent jN F.ExpN F.isExpN
  · exact F.D.exists_continuous_algebra_representation
      inferInstance jD F.ExpD F.isExpD
  · intro ρN ρD hN hD
    exact ⟨F.rotationRepresentation_conjugation hExp j ρN ρD hN hD,
      F.rotationRepresentation_overlap hExp j ρN ρD hN hD⟩

end ComplexWeightFactorModel
end PolycyclicRecognition

end

end OAI
