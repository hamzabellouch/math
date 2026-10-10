import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeRootWeyl
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeRootSections
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaComplexPointMeasure

namespace OAI

/-! Involutive action of the opposite cubic root on actual sections. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

theorem cubicThetaPrimeCubeRootWeylConjugate_involutive {p : Eisenstein} (hp : primaryPrime p) :
    Function.Involutive (cubicThetaPrimeCubeRootWeylConjugate hp) := by
  intro g
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  rw [cubicThetaPrimeCubeRootWeylConjugate_matrix]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j
  · simpa using congrArg (fun M : Matrix (Fin 2) (Fin 2) Eisenstein => M 1 1)
      (cubicThetaPrimeCubeRootWeylConjugate_matrix hp g)
  · have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) Eisenstein => M 1 0)
      (cubicThetaPrimeCubeRootWeylConjugate_matrix hp g)
    simp at he ⊢
    rw [he,show -((p^3)^2*g.val.val 0 1)=(p^3)^2*(-g.val.val 0 1) by ring,
      mul_div_cancel_left₀ _ (pow_ne_zero 2 (pow_ne_zero 3 hp.2.ne_zero)),neg_neg]
  · have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) Eisenstein => M 0 1)
      (cubicThetaPrimeCubeRootWeylConjugate_matrix hp g)
    simp at he ⊢
    rw [he]
    linear_combination cubicThetaPrimeCubeRoot_lower_division hp g
  · simpa using congrArg (fun M : Matrix (Fin 2) (Fin 2) Eisenstein => M 0 0)
      (cubicThetaPrimeCubeRootWeylConjugate_matrix hp g)

lemma cubicThetaPrimeCubeRootWeylPoint_intertwines {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeCubeRootSubgroup p) (y : CubicThetaPoint) :
    cubicThetaPrimeCubeRootWeylElement hp • (g.val • y)=
      (cubicThetaPrimeCubeRootWeylConjugate hp g).val • (cubicThetaPrimeCubeRootWeylElement hp • y) := by
  change cubicThetaPrimeCubeRootWeylElement hp • (cubicThetaPrincipalComplex g.val • y)=
    cubicThetaPrincipalComplex (cubicThetaPrimeCubeRootWeylConjugate hp g).val •
      (cubicThetaPrimeCubeRootWeylElement hp • y)
  rw [←mul_smul,←mul_smul,cubicThetaPrimeCubeRootWeyl_intertwines]


def cubicThetaPrimeCubeRootWeylSection {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeCubeRootSections p) : cubicThetaPrimeCubeRootSections p :=
  ⟨⟨fun y => F.val (cubicThetaPrimeCubeRootWeylElement hp • y),
    F.val.continuous.comp (continuous_const_smul _)⟩,by
    intro g y
    change F.val (cubicThetaPrimeCubeRootWeylElement hp • (g.val • y))=
      cubicThetaKubotaValue g.val*F.val (cubicThetaPrimeCubeRootWeylElement hp • y)
    rw [cubicThetaPrimeCubeRootWeylPoint_intertwines,F.property,cubicThetaPrimeCubeRootWeyl_kubota]⟩

lemma cubicThetaPrimeCubeRootWeylSection_involutive {p : Eisenstein} (hp : primaryPrime p) :
    Function.Involutive (cubicThetaPrimeCubeRootWeylSection hp) := by
  intro F
  apply Subtype.ext
  apply ContinuousMap.ext
  intro y
  change F.val (cubicThetaPrimeCubeRootWeylElement hp • (cubicThetaPrimeCubeRootWeylElement hp • y))=F.val y
  rw [cubicThetaPrimeCubeRootWeylPoint_involutive]

def cubicThetaPrimeCubeRootWeylOperator {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaPrimeCubeRootSections p ≃ₗ[ℂ] cubicThetaPrimeCubeRootSections p where
  toFun := cubicThetaPrimeCubeRootWeylSection hp
  invFun := cubicThetaPrimeCubeRootWeylSection hp
  left_inv := cubicThetaPrimeCubeRootWeylSection_involutive hp
  right_inv := cubicThetaPrimeCubeRootWeylSection_involutive hp
  map_add' _F _G := rfl
  map_smul' _c _F := rfl


end CubicFirstMoment

end

end OAI
