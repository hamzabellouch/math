import OAI.GroupTheory.PolycyclicRecognition.Algebra.AbelianH2CrossProduct
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.ExteriorSquareHomology

namespace OAI

/-! # The exterior cross product into second homology -/

noncomputable section
namespace PolycyclicRecognition
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable (A : Type) [CommGroup A]

def abelianH2AlternatingMap :
    Additive A [⋀^Fin 2]→ₗ[ℤ] groupHomology.H2 (integralTrivialCoefficient A) where
  toFun v := abelianH2Pairing (v 0) (v 1)
  map_update_add' := by
    intro _ v i x y
    fin_cases i <;> simp [Function.update, map_add, AddMonoidHom.add_apply]
  map_update_smul' := by
    intro _ v i z x
    fin_cases i
    · simpa [Function.update, AddMonoidHom.flip_apply] using
        map_intCast_smul (abelianH2Pairing.flip (v 1)) ℤ ℤ z x
    · simpa [Function.update] using
        map_intCast_smul (abelianH2Pairing (v 0)) ℤ ℤ z x
  map_eq_zero_of_eq' := by
    intro v i j h hij
    fin_cases i <;> fin_cases j <;> simp_all [abelianH2Pairing]

def abelianH2ExteriorProduct :
    (⋀[ℤ]^2 (Additive A)) →ₗ[ℤ] groupHomology.H2 (integralTrivialCoefficient A) :=
  exteriorPower.alternatingMapLinearEquiv (abelianH2AlternatingMap A)

@[simp] theorem abelianH2ExteriorProduct_value (a b : A) :
    abelianH2ExteriorProduct A (exteriorSquareValue (Additive.ofMul a) (Additive.ofMul b)) =
      abelianH2Class a b := by
  exact exteriorPower.alternatingMapLinearEquiv_apply_ιMulti
    (abelianH2AlternatingMap A) ![Additive.ofMul a, Additive.ofMul b]

theorem exteriorSquareHomology_comp_exteriorProduct :
    (exteriorSquareHomology A).comp (abelianH2ExteriorProduct A) =
      (2 : ℤ) • LinearMap.id := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  have hv : v = ![v 0, v 1] := by
    funext i
    fin_cases i <;> rfl
  change exteriorSquareHomology A
      (abelianH2ExteriorProduct A (exteriorPower.ιMulti ℤ 2 v)) =
    (2 : ℤ) • exteriorPower.ιMulti ℤ 2 v
  rw [hv]
  exact (congrArg (exteriorSquareHomology A)
    (abelianH2ExteriorProduct_value A (v 0).toMul (v 1).toMul)).trans
      (exteriorSquareHomology_antisymmetric A (v 0).toMul (v 1).toMul)

theorem abelianH2ExteriorProduct_injective
    (h2 : Function.Injective (fun x : ⋀[ℤ]^2 (Additive A) => (2 : ℤ) • x)) :
    Function.Injective (abelianH2ExteriorProduct A) := by
  intro x y h
  apply h2
  have hx := LinearMap.congr_fun (exteriorSquareHomology_comp_exteriorProduct A) x
  have hy := LinearMap.congr_fun (exteriorSquareHomology_comp_exteriorProduct A) y
  exact hx.symm.trans ((congrArg (exteriorSquareHomology A) h).trans hy)

end PolycyclicRecognition

end

end OAI
