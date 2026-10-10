import OAI.GroupTheory.PolycyclicRecognition.Geometry.RotationFactorProduct

namespace OAI

/-! # Global exponential factor coordinates and cancellation -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold

variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ,E)) ⊤ G]
  {a : ℕ} {T : ComplexTriangularAdjoint (GroupLieAlgebra (𝓘(ℝ,E)) G) a}
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ,E)) G)} [H.IsCartanSubalgebra]
  {Exp : GroupLieAlgebra (𝓘(ℝ,E)) G → G}

namespace ComplexWeightFactorModel
variable (F : ComplexWeightFactorModel T H Exp) (hExp : IsGroupExponential Exp)
attribute [local instance] semidirectProductTopology

def rotationExponentialProduct (p : T.kernelIdeal × H) : F.SmoothRotationalModification hExp :=
  F.nilpotentFactorToRotation hExp (F.ExpN (F.N.equiv p.1)) *
    F.cartanFactorToRotation hExp (F.ExpD (F.D.equiv p.2))

theorem rotationExponentialProduct_surjective :
    Function.Surjective (F.rotationExponentialProduct hExp) :=
  (F.rotationFactorProduct_surjective hExp).comp
    (F.expN_surjective.prodMap F.expD_surjective)

theorem rotationExponentialProduct_eq_one (x : T.kernelIdeal) (h : H)
    (hx : (x : GroupLieAlgebra (𝓘(ℝ,E)) G) = -(h : GroupLieAlgebra (𝓘(ℝ,E)) G)) :
    F.rotationExponentialProduct hExp (x,h) = 1 := by
  apply (F.smoothRotationalModificationHomeomorph hExp).injective
  change F.smoothRotationalModificationHomeomorph hExp
    (F.nilpotentFactorToRotation hExp (F.ExpN (F.N.equiv x)) *
      F.cartanFactorToRotation hExp (F.ExpD (F.D.equiv h))) = 1
  rw [F.rotationFactorProduct_coordinates, F.compatibleN, F.compatibleD, hx,
    hExp.map_neg, inv_mul_cancel]

end ComplexWeightFactorModel
end PolycyclicRecognition

end

end OAI
