import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeDoubleRootWeyl
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeDoubleRootSections
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaComplexPointMeasure

namespace OAI

/-! Involutive action of the opposite square root on actual sections. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

theorem cubicThetaPrimeDoubleRootWeylConjugate_involutive {p : Eisenstein} (hp : primaryPrime p) :
    Function.Involutive (cubicThetaPrimeDoubleRootWeylConjugate hp) := by
  intro g
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  rw [cubicThetaPrimeDoubleRootWeylConjugate_matrix]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j
  · simpa using congrArg (fun M : Matrix (Fin 2) (Fin 2) Eisenstein => M 1 1)
      (cubicThetaPrimeDoubleRootWeylConjugate_matrix hp g)
  · have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) Eisenstein => M 1 0)
      (cubicThetaPrimeDoubleRootWeylConjugate_matrix hp g)
    simp at he ⊢
    rw [he,show -((p^2)^2*g.val.val 0 1)=(p^2)^2*(-g.val.val 0 1) by ring,
      mul_div_cancel_left₀ _ (pow_ne_zero 2 (pow_ne_zero 2 hp.2.ne_zero)),neg_neg]
  · have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) Eisenstein => M 0 1)
      (cubicThetaPrimeDoubleRootWeylConjugate_matrix hp g)
    simp at he ⊢
    rw [he]
    linear_combination cubicThetaPrimeDoubleRoot_lower_division hp g
  · simpa using congrArg (fun M : Matrix (Fin 2) (Fin 2) Eisenstein => M 0 0)
      (cubicThetaPrimeDoubleRootWeylConjugate_matrix hp g)

lemma cubicThetaPrimeDoubleRootWeylPoint_intertwines {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeDoubleRootSubgroup p) (y : CubicThetaPoint) :
    cubicThetaPrimeDoubleRootWeylElement hp • (g.val • y)=
      (cubicThetaPrimeDoubleRootWeylConjugate hp g).val • (cubicThetaPrimeDoubleRootWeylElement hp • y) := by
  change cubicThetaPrimeDoubleRootWeylElement hp • (cubicThetaPrincipalComplex g.val • y)=
    cubicThetaPrincipalComplex (cubicThetaPrimeDoubleRootWeylConjugate hp g).val •
      (cubicThetaPrimeDoubleRootWeylElement hp • y)
  rw [←mul_smul,←mul_smul,cubicThetaPrimeDoubleRootWeyl_intertwines]


def cubicThetaPrimeDoubleRootWeylSection {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeDoubleRootSections p) : cubicThetaPrimeDoubleRootSections p :=
  ⟨⟨fun y => F.val (cubicThetaPrimeDoubleRootWeylElement hp • y),
    F.val.continuous.comp (continuous_const_smul _)⟩,by
    intro g y
    change F.val (cubicThetaPrimeDoubleRootWeylElement hp • (g.val • y))=
      cubicThetaKubotaValue g.val*F.val (cubicThetaPrimeDoubleRootWeylElement hp • y)
    rw [cubicThetaPrimeDoubleRootWeylPoint_intertwines,F.property,cubicThetaPrimeDoubleRootWeyl_kubota]⟩

lemma cubicThetaPrimeDoubleRootWeylSection_involutive {p : Eisenstein} (hp : primaryPrime p) :
    Function.Involutive (cubicThetaPrimeDoubleRootWeylSection hp) := by
  intro F
  apply Subtype.ext
  apply ContinuousMap.ext
  intro y
  change F.val (cubicThetaPrimeDoubleRootWeylElement hp • (cubicThetaPrimeDoubleRootWeylElement hp • y))=F.val y
  rw [cubicThetaPrimeDoubleRootWeylPoint_involutive]

def cubicThetaPrimeDoubleRootWeylOperator {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaPrimeDoubleRootSections p ≃ₗ[ℂ] cubicThetaPrimeDoubleRootSections p where
  toFun := cubicThetaPrimeDoubleRootWeylSection hp
  invFun := cubicThetaPrimeDoubleRootWeylSection hp
  left_inv := cubicThetaPrimeDoubleRootWeylSection_involutive hp
  right_inv := cubicThetaPrimeDoubleRootWeylSection_involutive hp
  map_add' _F _G := rfl
  map_smul' _c _F := rfl


end CubicFirstMoment

end

end OAI
