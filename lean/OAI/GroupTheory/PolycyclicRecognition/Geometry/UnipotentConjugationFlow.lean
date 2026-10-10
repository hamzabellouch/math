import OAI.GroupTheory.PolycyclicRecognition.Algebra.RealNilpotentLogIntertwiner
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialInnerLogarithm
import OAI.GroupTheory.PolycyclicRecognition.Geometry.UnipotentLieFlow
import OAI.GroupTheory.PolycyclicRecognition.Algebra.NilpotentIntrinsicIntegration

namespace OAI

/-! # An integral conjugation identity determines the real nilpotent flow -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff
variable {L M : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [RealNormedLieAlgebra M] [FiniteDimensional ℝ M]
  [Q : PolynomialExponentialCoordinates M] [LieRing.IsNilpotent M]

theorem unipotent_conjugation_log (A : L ≃ₗ⁅ℝ⁆ L)
    (hA : IsNilpotent (A.toLinearMap - 1)) (f : L →ₗ⁅ℝ⁆ M) (u : M)
    (h : ∀ x, f (A x) = u * f x * u⁻¹) (x : L) :
    f (unipotentLieLogarithm A hA x) = ⁅u, f x⁆ := by
  have hh := real_nilpotentLog_intertwiner f.toLinearMap
    (A.toLinearMap - 1) ((polynomialInnerLieEquiv u).toLinearMap - 1)
    hA (polynomial_inner_unipotent u) (by
      intro y
      change f (A y - y) = polynomialInnerLieEquiv u (f y) - f y
      rw [map_sub, h, polynomialInnerLieEquiv_apply]) x
  rw [polynomial_inner_log] at hh
  exact hh

theorem unipotent_conjugation_flow (A : L ≃ₗ⁅ℝ⁆ L)
    (hA : IsNilpotent (A.toLinearMap - 1)) (f : L →ₗ⁅ℝ⁆ M) (u : M)
    (h : ∀ x, f (A x) = u * f x * u⁻¹) (t : ℝ) (x : L) :
    f (unipotentLieFlow A hA t x) = (t • u) * f x * (t • u)⁻¹ := by
  have hh := derivationFlow_intrinsic_conjugation (unipotentLieLogarithm A hA)
    (unipotentLieLogarithm_nilpotent A hA)
    (fun v : GroupLieAlgebra (𝓘(ℝ, M)) M => (v : M))
    PolynomialExponentialCoordinates.isGroupExponential_identity
    (Q.tangentEquiv.toLinearMap.comp f.toLinearMap) (Q.tangentEquiv u)
    (by
      intro y
      change Q.tangentEquiv (f (unipotentLieLogarithm A hA y)) =
        ⁅Q.tangentEquiv u, Q.tangentEquiv (f y)⁆
      rw [unipotent_conjugation_log A hA f u h, Q.tangentEquiv.map_lie]) t x
  simp only [LinearMap.comp_apply, LieHom.coe_toLinearMap,
    LieEquiv.coe_toLieHom, Q.tangentEquiv_apply] at hh
  exact hh

end PolycyclicRecognition

end

end OAI
