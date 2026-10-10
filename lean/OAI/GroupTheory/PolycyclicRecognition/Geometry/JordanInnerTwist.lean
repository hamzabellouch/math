import OAI.GroupTheory.PolycyclicRecognition.Geometry.JordanLangTransversal
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialInnerUnipotence
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialDerivationAction
import OAI.GroupTheory.PolycyclicRecognition.Geometry.RealLieJordanDecomposition

namespace OAI

/-! # Jordan normal form after an arbitrary inner perturbation

The global Lang transversal moves the perturbing element into the fixed
subgroup of the semisimple factor. Its remaining inner action combines with
the unipotent factor without losing unipotence.
-/

noncomputable section
namespace PolycyclicRecognition
variable {L : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [C : PolynomialExponentialCoordinates L] [LieRing.IsNilpotent L]

theorem jordan_inner_twist_normal_form (A S U : L ≃ₗ⁅ℝ⁆ L)
    (hS : Module.End.IsSemisimple S.toLinearMap)
    (hU : IsNilpotent (U.toLinearMap - 1))
    (hSU : Commute S.toLinearMap U.toLinearMap)
    (hA : A.toLinearMap = S.toLinearMap * U.toLinearMap) (u : L) :
    ∃ (v : L) (W : L ≃ₗ⁅ℝ⁆ L), IsNilpotent (W.toLinearMap - 1) ∧
      Commute S.toLinearMap W.toLinearMap ∧
      ∀ x : L, v * (u * A (v⁻¹ * x * v) * u⁻¹) * v⁻¹ = S (W x) := by
  obtain ⟨v, w, _, hw, hu⟩ := jordan_lang_decomposition A S U hS hU hSU hA u
  let W := U.trans (polynomialInnerLieEquiv w)
  have hW (x : L) : W x = w * U x * w⁻¹ := polynomialInnerLieEquiv_apply w (U x)
  have hAx (x : L) : A x = S (U x) := LinearMap.congr_fun hA x
  have hSUx (x : L) : S (U x) = U (S x) := LinearMap.congr_fun hSU.eq x
  let s := PolynomialExponentialCoordinates.groupAutomorphism (P := C) S
  let a := PolynomialExponentialCoordinates.groupAutomorphism (P := C) A
  refine ⟨v, W, polynomial_inner_mul_unipotent U hU w, ?_, ?_⟩
  · apply LinearMap.ext
    intro x
    change S (W x) = W (S x)
    rw [hW, hW]
    change s (w * U x * w⁻¹) = w * U (S x) * w⁻¹
    rw [map_mul, map_mul, map_inv]
    change S w * S (U x) * (S w)⁻¹ = w * U (S x) * w⁻¹
    rw [hw, hSUx]
  · intro x
    have hr : v * (u * A (v⁻¹ * x * v) * u⁻¹) * v⁻¹ = w * A x * w⁻¹ := by
      change v * (u * a (v⁻¹ * x * v) * u⁻¹) * v⁻¹ = w * a x * w⁻¹
      change u = v⁻¹ * w * a v at hu
      rw [hu]
      simp only [map_mul, map_inv]
      group
    rw [hr, hW, hAx]
    change w * S (U x) * w⁻¹ = s (w * U x * w⁻¹)
    rw [map_mul, map_mul, map_inv]
    change w * S (U x) * w⁻¹ = S w * S (U x) * (S w)⁻¹
    rw [hw]

theorem inner_twist_has_original_semisimple_normal_form (A : L ≃ₗ⁅ℝ⁆ L) :
    ∃ S : L ≃ₗ⁅ℝ⁆ L, Module.End.IsSemisimple S.toLinearMap ∧
      ∀ u : L, ∃ (v : L) (W : L ≃ₗ⁅ℝ⁆ L), IsNilpotent (W.toLinearMap - 1) ∧
        Commute S.toLinearMap W.toLinearMap ∧
        ∀ x : L, v * (u * A (v⁻¹ * x * v) * u⁻¹) * v⁻¹ = S (W x) := by
  obtain ⟨S, U, hS, hU, hSU, hA⟩ := real_lie_jordan_decomposition A
  exact ⟨S, hS, fun u => jordan_inner_twist_normal_form A S U hS hU hSU hA u⟩

end PolycyclicRecognition

end

end OAI
