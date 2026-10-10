import OAI.GroupTheory.PolycyclicRecognition.Algebra.SemisimpleMovingAction
import OAI.GroupTheory.PolycyclicRecognition.Geometry.JordanTransversalLinearMap

namespace OAI

/-! # Bijective Lang maps on the moving central factor

The unipotent factor causes no fixed directions on the range of S-1. The
central group's Lang map is exactly that invertible linear difference.
-/

noncomputable section
namespace PolycyclicRecognition
attribute [local instance] LieRing.ofAssociativeRing polynomialSubalgebraGroup
variable {L : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]

def semisimpleMovingDifference (S T : L ≃ₗ⁅ℝ⁆ L)
    (hST : Commute S.toLinearMap T.toLinearMap) :
    Module.End ℝ (semisimpleMovingCenter S) :=
  (T.toLinearMap - 1).restrict (fun x hx => (semisimpleMovingCenter S).sub_mem
    (commuting_lieEquiv_preserves_movingCenter S T hST x hx) hx)

theorem semisimpleMovingDifference_bijective (S U T : L ≃ₗ⁅ℝ⁆ L)
    (hS : Module.End.IsSemisimple S.toLinearMap)
    (hU : IsNilpotent (U.toLinearMap - 1))
    (hSU : Commute S.toLinearMap U.toLinearMap)
    (hST : Commute S.toLinearMap T.toLinearMap)
    (hT : T.toLinearMap = S.toLinearMap * U.toLinearMap) :
    Function.Bijective (semisimpleMovingDifference S T hST) := by
  let p := semisimpleOneProjection S.toLinearMap hS
  let e : Module.End ℝ L := (S.toLinearMap * U.toLinearMap - 1) * (1 - p) + p
  have hb : Function.Bijective e := jordan_transversal_linear_bijective
    S.toLinearMap U.toLinearMap hS hU hSU
  have he (x : semisimpleMovingCenter S) : e x = T x - x := by
    have hp : p x = 0 := Submodule.projection_apply_of_mem_right _ x.property.2
    change S (U ((x : L) - p x)) - ((x : L) - p x) + p x = T x - x
    rw [hp, sub_zero, add_zero]
    have ht : T x = S (U x) := LinearMap.congr_fun hT x
    rw [ht]
  have hi : Function.Injective (semisimpleMovingDifference S T hST) := by
    intro x y h
    apply Subtype.ext
    apply hb.injective
    rw [he, he]
    exact congrArg Subtype.val h
  exact ⟨hi, LinearMap.injective_iff_surjective.mp hi⟩

variable [P : PolynomialExponentialCoordinates L]

theorem semisimpleMoving_lang_eq_difference (S T : L ≃ₗ⁅ℝ⁆ L)
    (hST : Commute S.toLinearMap T.toLinearMap) (x : semisimpleMovingCenter S) :
    x⁻¹ * semisimpleMovingGroupAction S T hST x = semisimpleMovingDifference S T hST x := by
  apply Subtype.ext
  change (x : L)⁻¹ * T x = T x - x
  have hz : ⁅-(x : L), T x⁆ = 0 := by
    rw [neg_lie]
    have hh : ⁅(x : L), T x⁆ = 0 := LinearMap.congr_fun x.property.1 (T x)
    rw [hh, neg_zero]
  rw [P.inv_eq_neg, polynomial_mul_eq_add_of_lie_eq_zero _ _ hz]
  abel

theorem semisimpleMoving_lang_bijective (S U T : L ≃ₗ⁅ℝ⁆ L)
    (hS : Module.End.IsSemisimple S.toLinearMap)
    (hU : IsNilpotent (U.toLinearMap - 1))
    (hSU : Commute S.toLinearMap U.toLinearMap)
    (hST : Commute S.toLinearMap T.toLinearMap)
    (hT : T.toLinearMap = S.toLinearMap * U.toLinearMap) :
    Function.Bijective (fun x : semisimpleMovingCenter S =>
      x⁻¹ * semisimpleMovingGroupAction S T hST x) := by
  have he : (fun x : semisimpleMovingCenter S =>
      x⁻¹ * semisimpleMovingGroupAction S T hST x) = semisimpleMovingDifference S T hST := by
    funext x
    exact semisimpleMoving_lang_eq_difference S T hST x
  rw [he]
  exact semisimpleMovingDifference_bijective S U T hS hU hSU hST hT

end PolycyclicRecognition

end

end OAI
