import OAI.GroupTheory.PolycyclicRecognition.Algebra.InnerCentralizerProduct
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialInnerLogarithm

namespace OAI

/-! # The Lie subalgebra is the actual inner-action centralizer

The exact finite logarithm identifies the group condition with centrality of
Sx-x. This connects the product decomposition to kernels of group extensions.
-/

noncomputable section
namespace PolycyclicRecognition
attribute [local instance] LieRing.ofAssociativeRing
variable {L : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] [LieRing.IsNilpotent L]

theorem mem_innerCentralizerLieSubalgebra_iff (S : L ≃ₗ⁅ℝ⁆ L) (x : L) :
    x ∈ innerCentralizerLieSubalgebra S ↔
      Commute S.toLinearMap (polynomialInnerLieEquiv x).toLinearMap := by
  let s := PolynomialExponentialCoordinates.groupAutomorphism (P := P) S
  have he (y : L) : S (polynomialInnerLieEquiv x y) =
      polynomialInnerLieEquiv (S x) (S y) := by
    rw [polynomialInnerLieEquiv_apply, polynomialInnerLieEquiv_apply]
    change s (x * y * x⁻¹) = s x * s y * (s x)⁻¹
    rw [map_mul, map_mul, map_inv]
  constructor
  · intro hx
    have hd : LieAlgebra.ad ℝ L (S x) = LieAlgebra.ad ℝ L x := by
      change LieAlgebra.ad ℝ L (S x - x) = 0 at hx
      rwa [map_sub, sub_eq_zero] at hx
    have hi := polynomial_inner_eq_of_ad_eq (S x) x hd
    apply LinearMap.ext
    intro y
    change S (polynomialInnerLieEquiv x y) = polynomialInnerLieEquiv x (S y)
    rw [he]
    exact LinearMap.congr_fun hi (S y)
  · intro hc
    have hi : (polynomialInnerLieEquiv (S x)).toLinearMap =
        (polynomialInnerLieEquiv x).toLinearMap := by
      apply LinearMap.ext
      intro y
      have hh : S (polynomialInnerLieEquiv x (S.symm y)) =
          polynomialInnerLieEquiv x (S (S.symm y)) :=
        LinearMap.congr_fun hc.eq (S.symm y)
      rw [he, S.apply_symm_apply] at hh
      exact hh
    change LieAlgebra.ad ℝ L (S x - x) = 0
    rw [map_sub, polynomial_inner_eq_implies_ad_eq (S x) x hi, sub_self]

end PolycyclicRecognition

end

end OAI
