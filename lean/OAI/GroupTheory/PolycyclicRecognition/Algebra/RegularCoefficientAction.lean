import OAI.GroupTheory.PolycyclicRecognition.Algebra.RegularDualRepresentation
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

namespace OAI

/-! # Inverse coefficient action in the regular-dual pairing -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory
open scoped MonoidAlgebra
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
variable {G : Type} [Group G]

def regularCoefficientAction (A : Rep ℤ G) : ℤ[G] →ₗ[ℤ] (A →ₗ[ℤ] A) :=
  (Finsupp.linearCombination ℤ (fun g : G => A.ρ g⁻¹)).comp
    (MonoidAlgebra.coeffLinearEquiv ℤ).toLinearMap

@[simp] theorem regularCoefficientAction_single (A : Rep ℤ G) (g : G) (r : ℤ) :
    regularCoefficientAction A (MonoidAlgebra.single g r) = r • A.ρ g⁻¹ := by
  simp [regularCoefficientAction]

theorem regularCoefficientAction_rightTranslation (A : Rep ℤ G) (g : G) (q : ℤ[G]) :
    regularCoefficientAction A ((regularRightTranslation g).hom q) =
      A.ρ g ∘ₗ regularCoefficientAction A q := by
  induction q using MonoidAlgebra.induction_on with
  | of h =>
    rw [MonoidAlgebra.of_apply, regularRightTranslation_single]
    simp only [regularCoefficientAction_single, one_smul, mul_inv_rev, inv_inv,
      map_mul, Module.End.mul_eq_comp]
  | add x y hx hy => simp only [map_add, hx, hy, LinearMap.comp_add]
  | smul r x hx =>
    simp only [map_smul, hx]
    ext a
    change r • (A.ρ g (regularCoefficientAction A x a)) =
      A.ρ g (r • regularCoefficientAction A x a)
    exact (map_zsmul (A.ρ g) r (regularCoefficientAction A x a)).symm

theorem regularCoefficientAction_leftTranslation (A : Rep ℤ G) (g : G) (q : ℤ[G]) :
    regularCoefficientAction A ((Rep.leftRegular ℤ G).ρ g q) =
      regularCoefficientAction A q ∘ₗ A.ρ g⁻¹ := by
  induction q using MonoidAlgebra.induction_on with
  | of h =>
    simp only [MonoidAlgebra.of_apply, Representation.ofMulAction_single,
      smul_eq_mul, regularCoefficientAction_single, one_smul, mul_inv_rev,
      map_mul, Module.End.mul_eq_comp]
  | add x y hx hy => simp only [map_add, hx, hy, LinearMap.add_comp]
  | smul r x hx => simp only [map_smul, hx, LinearMap.smul_comp]

end PolycyclicRecognition

end

end OAI
