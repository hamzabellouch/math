import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialInnerUnipotence
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialDerivationAction

namespace OAI

/-! # A correction fixed by the semisimple factor preserves that factor -/

noncomputable section
namespace PolycyclicRecognition
variable {L : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [C : PolynomialExponentialCoordinates L] [LieRing.IsNilpotent L]

theorem inner_correction_preserves_jordan_factor (A S U : L ≃ₗ⁅ℝ⁆ L)
    (hU : IsNilpotent (U.toLinearMap - 1))
    (hSU : Commute S.toLinearMap U.toLinearMap)
    (hA : A.toLinearMap = S.toLinearMap * U.toLinearMap)
    (v : L) (hSv : S v = v) :
    ∃ W : L ≃ₗ⁅ℝ⁆ L, IsNilpotent (W.toLinearMap - 1) ∧
      Commute S.toLinearMap W.toLinearMap ∧
      (polynomialInnerLieEquiv v).toLinearMap * A.toLinearMap = S.toLinearMap * W.toLinearMap := by
  let W := U.trans (polynomialInnerLieEquiv v)
  have hW (x : L) : W x = v * U x * v⁻¹ := polynomialInnerLieEquiv_apply v (U x)
  let s := PolynomialExponentialCoordinates.groupAutomorphism (P := C) S
  have hnatural (x : L) : S (v * x * v⁻¹) = v * S x * v⁻¹ := by
    change s (v * x * v⁻¹) = v * s x * v⁻¹
    rw [map_mul, map_mul, map_inv]
    change S v * S x * (S v)⁻¹ = v * S x * v⁻¹
    rw [hSv]
  refine ⟨W, polynomial_inner_mul_unipotent U hU v, ?_, ?_⟩
  · apply LinearMap.ext
    intro x
    change S (W x) = W (S x)
    rw [hW, hW, hnatural]
    have hh : S (U x) = U (S x) := LinearMap.congr_fun hSU.eq x
    rw [hh]
  · apply LinearMap.ext
    intro x
    change polynomialInnerLieEquiv v (A x) = S (W x)
    rw [hW, hnatural, polynomialInnerLieEquiv_apply]
    have hh : A x = S (U x) := LinearMap.congr_fun hA x
    rw [hh]

end PolycyclicRecognition

end

end OAI
