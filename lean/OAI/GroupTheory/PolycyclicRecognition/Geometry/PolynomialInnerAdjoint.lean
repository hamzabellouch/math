import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialModelHom
import OAI.GroupTheory.PolycyclicRecognition.Geometry.IntrinsicAdjointExponential

namespace OAI

/-! # Inner conjugation in the concrete exponential coordinates -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold
attribute [local instance] LieRing.ofAssociativeRing
variable {L : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L]

theorem polynomial_adjoint_apply (u x : L) :
    adjointLinearMap (E := L) u x = u * x * u⁻¹ := by
  have h := PolynomialExponentialCoordinates.isGroupExponential_identity.map_of_mdifferentiable
    (PolynomialExponentialCoordinates.isGroupExponential_identity (L := L))
    (MulAut.conj u).toMonoidHom ((contMDiff_conjugation u).mdifferentiable (by simp)) x
  exact h.symm

theorem polynomial_adjointOperator (u : L) :
    groupAdjointOperator (P.tangentEquiv u) =
      LinearMap.toContinuousLinearMap (LieAlgebra.ad ℝ L u) := by
  apply ContinuousLinearMap.ext
  intro v
  have h := (P.tangentEquiv.map_lie u v).symm
  rw [P.tangentEquiv_apply v, P.tangentEquiv_apply ⁅u, v⁆] at h
  exact h

theorem polynomial_inner_eq_exp_ad (u x : L) :
    u * x * u⁻¹ = NormedSpace.exp (LinearMap.toContinuousLinearMap (LieAlgebra.ad ℝ L u)) x := by
  have h := adjointLinearMap_exponential
    (PolynomialExponentialCoordinates.isGroupExponential_identity (L := L)) (P.tangentEquiv u) 1
  rw [one_smul, polynomial_adjointOperator, P.tangentEquiv_apply] at h
  simp only [one_smul] at h
  rw [← polynomial_adjoint_apply u x, h]

end PolycyclicRecognition

end

end OAI
