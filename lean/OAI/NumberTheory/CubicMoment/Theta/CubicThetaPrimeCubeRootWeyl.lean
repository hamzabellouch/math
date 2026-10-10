import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeRootConjugation
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeAtkin
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaInversionInvolutive

namespace OAI

/-! The actual opposite-root involution at modulus p cubed. Both
integral conjugations preserve the original cubic automorphy factor. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

def cubicThetaPrimeCubeRootDilationIwahori {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeCubeRootSubgroup p) : cubicThetaPrimeIwahori (p^3) :=
  ⟨cubicThetaPrimeConjugate (cubicThetaPrimeCube_primary hp) (cubicThetaPrimeCubeRootIwahori g),by
    change p^3∣g.val.val 1 0/p^3
    rw [cubicThetaPrimeCubeRoot_lower_single_division hp g]
    exact dvd_mul_right _ _⟩

lemma cubicThetaPrimeCubeRootDilationIwahori_matrix {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeCubeRootSubgroup p) :
    ((cubicThetaPrimeCubeRootDilationIwahori hp g).val.val : Matrix (Fin 2) (Fin 2) Eisenstein)=
      !![g.val.val 0 0,p^3*g.val.val 0 1;g.val.val 1 0/p^3,g.val.val 1 1] := rfl

lemma cubicThetaPrimeCubeRootDilationIwahori_entry00 {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeCubeRootSubgroup p) :
    (cubicThetaPrimeCubeRootDilationIwahori hp g).val.val 0 0=g.val.val 0 0 := rfl

lemma cubicThetaPrimeCubeRootDilationIwahori_entry01 {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeCubeRootSubgroup p) :
    (cubicThetaPrimeCubeRootDilationIwahori hp g).val.val 0 1=p^3*g.val.val 0 1 := rfl

lemma cubicThetaPrimeCubeRootDilationIwahori_entry10 {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeCubeRootSubgroup p) :
    (cubicThetaPrimeCubeRootDilationIwahori hp g).val.val 1 0=g.val.val 1 0/p^3 := rfl

lemma cubicThetaPrimeCubeRootDilationIwahori_entry11 {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeCubeRootSubgroup p) :
    (cubicThetaPrimeCubeRootDilationIwahori hp g).val.val 1 1=g.val.val 1 1 := rfl

lemma cubicThetaPrimeCubeRootWeylRaw_matrix {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeCubeRootSubgroup p) :
    ((cubicThetaPrimeCubeAtkinConjugate hp (cubicThetaPrimeCubeRootDilationIwahori hp g)).val.val :
      Matrix (Fin 2) (Fin 2) Eisenstein)=
      !![g.val.val 1 1,-(g.val.val 1 0/(p^3)^2);-(p^3)^2*g.val.val 0 1,g.val.val 0 0] := by
  have he := cubicThetaPrimeCubeAtkinConjugate_matrix hp (cubicThetaPrimeCubeRootDilationIwahori hp g)
  rw [cubicThetaPrimeCubeRootDilationIwahori_entry00,
    cubicThetaPrimeCubeRootDilationIwahori_entry01,
    cubicThetaPrimeCubeRootDilationIwahori_entry10,
    cubicThetaPrimeCubeRootDilationIwahori_entry11] at he
  rw [he,cubicThetaPrimeCubeRoot_lower_single_division hp g,
    mul_div_cancel_left₀ _ (pow_ne_zero 3 hp.2.ne_zero)]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [pow_two,mul_assoc]

def cubicThetaPrimeCubeRootWeylConjugate {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeCubeRootSubgroup p) : cubicThetaPrimeCubeRootSubgroup p :=
  ⟨(cubicThetaPrimeCubeAtkinConjugate hp (cubicThetaPrimeCubeRootDilationIwahori hp g)).val,by
    change (p^3)^2∣(cubicThetaPrimeCubeAtkinConjugate hp
      (cubicThetaPrimeCubeRootDilationIwahori hp g)).val.val 1 0 ∧
      p^3∣(cubicThetaPrimeCubeAtkinConjugate hp
      (cubicThetaPrimeCubeRootDilationIwahori hp g)).val.val 0 0-
      (cubicThetaPrimeCubeAtkinConjugate hp (cubicThetaPrimeCubeRootDilationIwahori hp g)).val.val 1 1
    rw [cubicThetaPrimeCubeRootWeylRaw_matrix]
    constructor
    · exact ⟨-g.val.val 0 1,by simp⟩
    · simpa only [Matrix.of_apply,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,neg_sub]
        using dvd_neg.mpr g.property.2⟩

lemma cubicThetaPrimeCubeRootWeylConjugate_matrix {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeCubeRootSubgroup p) :
    ((cubicThetaPrimeCubeRootWeylConjugate hp g).val.val : Matrix (Fin 2) (Fin 2) Eisenstein)=
      !![g.val.val 1 1,-(g.val.val 1 0/(p^3)^2);-(p^3)^2*g.val.val 0 1,g.val.val 0 0] :=
  cubicThetaPrimeCubeRootWeylRaw_matrix hp g

lemma cubicThetaPrimeCubeRootWeyl_kubota {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeCubeRootSubgroup p) :
    cubicThetaKubotaValue (cubicThetaPrimeCubeRootWeylConjugate hp g).val=cubicThetaKubotaValue g.val := by
  exact (cubicThetaPrimeCubeAtkinConjugate_kubota hp _).trans
    (cubicThetaPrimeCubeConjugate_kubota hp (cubicThetaPrimeCubeRootIwahori g)).symm

def cubicThetaPrimeCubeRootWeylElement {p : Eisenstein} (hp : primaryPrime p) : SL(2,ℂ) :=
  cubicThetaPrimeCubeAtkinMatrix hp*cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero)

theorem cubicThetaPrimeCubeRootWeyl_intertwines {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeCubeRootSubgroup p) :
    cubicThetaPrimeCubeRootWeylElement hp*cubicThetaPrincipalComplex g.val=
      cubicThetaPrincipalComplex (cubicThetaPrimeCubeRootWeylConjugate hp g).val*
        cubicThetaPrimeCubeRootWeylElement hp := by
  have hD : cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero)*cubicThetaPrincipalComplex g.val=
      cubicThetaPrincipalComplex (cubicThetaPrimeCubeRootDilationIwahori hp g).val*
        cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) :=
    cubicThetaPrimeDilation_intertwines (cubicThetaPrimeCube_primary hp) (cubicThetaPrimeCubeRootIwahori g)
  have hW : cubicThetaPrimeCubeAtkinMatrix hp*
      cubicThetaPrincipalComplex (cubicThetaPrimeCubeRootDilationIwahori hp g).val=
      cubicThetaPrincipalComplex (cubicThetaPrimeCubeRootWeylConjugate hp g).val*cubicThetaPrimeCubeAtkinMatrix hp :=
    cubicThetaPrimeCubeAtkinMatrix_intertwines hp (cubicThetaPrimeCubeRootDilationIwahori hp g)
  unfold cubicThetaPrimeCubeRootWeylElement
  rw [mul_assoc,hD,←mul_assoc,hW,mul_assoc]

lemma cubicThetaPrimeCubeRootWeylElement_inversion {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaPrimeCubeRootWeylElement hp=cubicThetaInversionMatrix ((p^3:Eisenstein):ℂ)
      (fun he => (pow_ne_zero 3 hp.2.ne_zero) (Subtype.ext he)) := by
  rw [cubicThetaPrimeCubeRootWeylElement,cubicThetaPrimeCubeAtkinMatrix,cubicThetaFullInversion_complex]
  apply Subtype.ext
  change ((cubicThetaInversionMatrix 1 one_ne_zero:Matrix (Fin 2) (Fin 2) ℂ)*
    (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero):Matrix (Fin 2) (Fin 2) ℂ))*
      (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero):Matrix (Fin 2) (Fin 2) ℂ)=_
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [cubicThetaInversionMatrix,cubicThetaPrimeDilation,Matrix.mul_apply,Fin.sum_univ_two,
      ←pow_two,cubicThetaPrimeSquareRoot_sq]

lemma cubicThetaPrimeCubeRootWeylPoint_involutive {p : Eisenstein} (hp : primaryPrime p)
    (y : CubicThetaPoint) :
    cubicThetaPrimeCubeRootWeylElement hp • (cubicThetaPrimeCubeRootWeylElement hp • y)=y := by
  apply Subtype.ext
  change cubicThetaMobius (cubicThetaPrimeCubeRootWeylElement hp)
    (cubicThetaMobius (cubicThetaPrimeCubeRootWeylElement hp) y.val)=y.val
  rw [cubicThetaPrimeCubeRootWeylElement_inversion,
    cubicThetaMobius_inversion _ (cubicThetaMobius_height_pos _ y.property),
    cubicThetaMobius_inversion _ y.property]
  exact cubicThetaInversion_involutive
    (fun he => (pow_ne_zero 3 hp.2.ne_zero) (Subtype.ext he)) y.property

end CubicFirstMoment

end

end OAI
