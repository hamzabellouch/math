import OAI.GroupTheory.PolycyclicRecognition.Geometry.RotationRepresentationIntegration
import OAI.GroupTheory.PolycyclicRecognition.Geometry.RealShadowRepresentation
import OAI.GroupTheory.PolycyclicRecognition.Geometry.TriangularMatrixExponentialInjective
import OAI.GroupTheory.PolycyclicRecognition.Algebra.RepresentationKernelCoordinates
import OAI.GroupTheory.PolycyclicRecognition.Geometry.RotationExponentialProduct

namespace OAI

/-! # Faithfulness from the two exponential factors -/

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

theorem rotationRepresentation_faithful {m : ℕ}
    (j : CartanRealShadow T H →ₗ⁅ℝ⁆ Matrix (Fin m) (Fin m) ℝ)
    (hj : Function.Injective j) (hu : ∀ x, (j x).IsUpperTriangular)
    (ρ : F.SmoothRotationalModification hExp →* (Matrix (Fin m) (Fin m) ℝ)ˣ)
    (he : ∀ (x : T.kernelIdeal) (h : H),
      ρ (F.nilpotentFactorToRotation hExp (F.ExpN (F.N.equiv x)) *
        F.cartanFactorToRotation hExp (F.ExpD (F.D.equiv h))) =
        algebraExpUnit (j (cartanRealShadowEquiv T H x)) *
          algebraExpUnit (j (cartanRealShadowEquiv T H h))) :
    Function.Injective ρ := by
  let f := F.rotationExponentialProduct hExp
  have hf : Function.Surjective f := F.rotationExponentialProduct_surjective hExp
  apply injective_of_kernel_in_coordinates ρ f hf
  rintro ⟨x,h⟩ hg
  change ρ (F.nilpotentFactorToRotation hExp (F.ExpN (F.N.equiv x)) *
      F.cartanFactorToRotation hExp (F.ExpD (F.D.equiv h))) = 1 at hg
  rw [he] at hg
  have ht := triangular_units_product_eq_one_imp_neg j.toLinearMap hj hu
    (cartanRealShadowEquiv T H x) (cartanRealShadowEquiv T H h) hg
  have hx : (x : GroupLieAlgebra (𝓘(ℝ,E)) G) = -(h : GroupLieAlgebra (𝓘(ℝ,E)) G) := by
    apply (cartanRealShadowEquiv T H).injective
    simpa only [map_neg] using ht
  exact F.rotationExponentialProduct_eq_one hExp x h hx

end ComplexWeightFactorModel
end PolycyclicRecognition

end

end OAI
