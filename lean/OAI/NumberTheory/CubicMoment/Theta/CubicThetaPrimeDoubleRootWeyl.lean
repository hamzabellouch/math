import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeDoubleRootConjugation
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeDoubleAtkin
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaInversionInvolutive

namespace OAI

/-! The actual opposite-root involution at modulus p cubed. Both
integral conjugations preserve the original cubic automorphy factor. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

def cubicThetaPrimeDoubleRootDilationIwahori {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeDoubleRootSubgroup p) : cubicThetaPrimeIwahori (p^2) :=
  ⟨cubicThetaPrimeConjugate (cubicThetaPrimeDouble_primary hp) (cubicThetaPrimeDoubleRootIwahori g),by
    change p^2∣g.val.val 1 0/p^2
    rw [cubicThetaPrimeDoubleRoot_lower_single_division hp g]
    exact dvd_mul_right _ _⟩

lemma cubicThetaPrimeDoubleRootDilationIwahori_matrix {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeDoubleRootSubgroup p) :
    ((cubicThetaPrimeDoubleRootDilationIwahori hp g).val.val : Matrix (Fin 2) (Fin 2) Eisenstein)=
      !![g.val.val 0 0,p^2*g.val.val 0 1;g.val.val 1 0/p^2,g.val.val 1 1] := rfl

lemma cubicThetaPrimeDoubleRootDilationIwahori_entry00 {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeDoubleRootSubgroup p) :
    (cubicThetaPrimeDoubleRootDilationIwahori hp g).val.val 0 0=g.val.val 0 0 := rfl

lemma cubicThetaPrimeDoubleRootDilationIwahori_entry01 {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeDoubleRootSubgroup p) :
    (cubicThetaPrimeDoubleRootDilationIwahori hp g).val.val 0 1=p^2*g.val.val 0 1 := rfl

lemma cubicThetaPrimeDoubleRootDilationIwahori_entry10 {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeDoubleRootSubgroup p) :
    (cubicThetaPrimeDoubleRootDilationIwahori hp g).val.val 1 0=g.val.val 1 0/p^2 := rfl

lemma cubicThetaPrimeDoubleRootDilationIwahori_entry11 {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeDoubleRootSubgroup p) :
    (cubicThetaPrimeDoubleRootDilationIwahori hp g).val.val 1 1=g.val.val 1 1 := rfl

lemma cubicThetaPrimeDoubleRootWeylRaw_matrix {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeDoubleRootSubgroup p) :
    ((cubicThetaPrimeDoubleAtkinConjugate hp (cubicThetaPrimeDoubleRootDilationIwahori hp g)).val.val :
      Matrix (Fin 2) (Fin 2) Eisenstein)=
      !![g.val.val 1 1,-(g.val.val 1 0/(p^2)^2);-(p^2)^2*g.val.val 0 1,g.val.val 0 0] := by
  have he := cubicThetaPrimeDoubleAtkinConjugate_matrix hp (cubicThetaPrimeDoubleRootDilationIwahori hp g)
  rw [cubicThetaPrimeDoubleRootDilationIwahori_entry00,
    cubicThetaPrimeDoubleRootDilationIwahori_entry01,
    cubicThetaPrimeDoubleRootDilationIwahori_entry10,
    cubicThetaPrimeDoubleRootDilationIwahori_entry11] at he
  rw [he,cubicThetaPrimeDoubleRoot_lower_single_division hp g,
    mul_div_cancel_left₀ _ (pow_ne_zero 2 hp.2.ne_zero)]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [pow_two,mul_assoc]

def cubicThetaPrimeDoubleRootWeylConjugate {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeDoubleRootSubgroup p) : cubicThetaPrimeDoubleRootSubgroup p :=
  ⟨(cubicThetaPrimeDoubleAtkinConjugate hp (cubicThetaPrimeDoubleRootDilationIwahori hp g)).val,by
    change (p^2)^2∣(cubicThetaPrimeDoubleAtkinConjugate hp
      (cubicThetaPrimeDoubleRootDilationIwahori hp g)).val.val 1 0 ∧
      p^2∣(cubicThetaPrimeDoubleAtkinConjugate hp
      (cubicThetaPrimeDoubleRootDilationIwahori hp g)).val.val 0 0-
      (cubicThetaPrimeDoubleAtkinConjugate hp (cubicThetaPrimeDoubleRootDilationIwahori hp g)).val.val 1 1
    rw [cubicThetaPrimeDoubleRootWeylRaw_matrix]
    constructor
    · exact ⟨-g.val.val 0 1,by simp⟩
    · simpa only [Matrix.of_apply,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,neg_sub]
        using dvd_neg.mpr g.property.2⟩

lemma cubicThetaPrimeDoubleRootWeylConjugate_matrix {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeDoubleRootSubgroup p) :
    ((cubicThetaPrimeDoubleRootWeylConjugate hp g).val.val : Matrix (Fin 2) (Fin 2) Eisenstein)=
      !![g.val.val 1 1,-(g.val.val 1 0/(p^2)^2);-(p^2)^2*g.val.val 0 1,g.val.val 0 0] :=
  cubicThetaPrimeDoubleRootWeylRaw_matrix hp g

lemma cubicThetaPrimeDoubleRootWeyl_kubota {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeDoubleRootSubgroup p) :
    cubicThetaKubotaValue (cubicThetaPrimeDoubleRootWeylConjugate hp g).val=cubicThetaKubotaValue g.val := by
  change cubicThetaKubotaValue (cubicThetaPrincipalConjugate cubicThetaFullInversion⁻¹
    (cubicThetaPrimeConjugate (cubicThetaPrimeDouble_primary hp)
      (cubicThetaPrimeDoubleRootDilationIwahori hp g)))=cubicThetaKubotaValue g.val
  rw [cubicThetaInversionConjugate_character]
  have he := cubicThetaPrimePowerConjugate_kubota_star hp 2
    (cubicThetaPrimeDoubleRootDilationIwahori hp g)
  change cubicThetaKubotaValue (cubicThetaPrimeConjugate (cubicThetaPrimeDouble_primary hp)
    (cubicThetaPrimeDoubleRootDilationIwahori hp g))=
    star ((cubicSymbol p (g.val.val 0 0))^2)*
      cubicThetaKubotaValue (cubicThetaPrimeDoubleRootDilationIwahori hp g).val at he
  rw [cubicThetaPrimeDoubleRoot_diagonal_character hp g,one_pow,star_one,one_mul] at he
  exact he.trans (cubicThetaPrimeDoubleRootDilation_kubota hp g)


def cubicThetaPrimeDoubleRootWeylElement {p : Eisenstein} (hp : primaryPrime p) : SL(2,ℂ) :=
  cubicThetaPrimeDoubleAtkinMatrix hp*cubicThetaPrimeDilation (pow_ne_zero 2 hp.2.ne_zero)

theorem cubicThetaPrimeDoubleRootWeyl_intertwines {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeDoubleRootSubgroup p) :
    cubicThetaPrimeDoubleRootWeylElement hp*cubicThetaPrincipalComplex g.val=
      cubicThetaPrincipalComplex (cubicThetaPrimeDoubleRootWeylConjugate hp g).val*
        cubicThetaPrimeDoubleRootWeylElement hp := by
  have hD : cubicThetaPrimeDilation (pow_ne_zero 2 hp.2.ne_zero)*cubicThetaPrincipalComplex g.val=
      cubicThetaPrincipalComplex (cubicThetaPrimeDoubleRootDilationIwahori hp g).val*
        cubicThetaPrimeDilation (pow_ne_zero 2 hp.2.ne_zero) :=
    cubicThetaPrimeDilation_intertwines (cubicThetaPrimeDouble_primary hp) (cubicThetaPrimeDoubleRootIwahori g)
  have hW : cubicThetaPrimeDoubleAtkinMatrix hp*
      cubicThetaPrincipalComplex (cubicThetaPrimeDoubleRootDilationIwahori hp g).val=
      cubicThetaPrincipalComplex (cubicThetaPrimeDoubleRootWeylConjugate hp g).val*cubicThetaPrimeDoubleAtkinMatrix hp :=
    cubicThetaPrimeDoubleAtkinMatrix_intertwines hp (cubicThetaPrimeDoubleRootDilationIwahori hp g)
  unfold cubicThetaPrimeDoubleRootWeylElement
  rw [mul_assoc,hD,←mul_assoc,hW,mul_assoc]

lemma cubicThetaPrimeDoubleRootWeylElement_inversion {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaPrimeDoubleRootWeylElement hp=cubicThetaInversionMatrix ((p^2:Eisenstein):ℂ)
      (fun he => (pow_ne_zero 2 hp.2.ne_zero) (Subtype.ext he)) := by
  rw [cubicThetaPrimeDoubleRootWeylElement,cubicThetaPrimeDoubleAtkinMatrix,cubicThetaFullInversion_complex]
  apply Subtype.ext
  change ((cubicThetaInversionMatrix 1 one_ne_zero:Matrix (Fin 2) (Fin 2) ℂ)*
    (cubicThetaPrimeDilation (pow_ne_zero 2 hp.2.ne_zero):Matrix (Fin 2) (Fin 2) ℂ))*
      (cubicThetaPrimeDilation (pow_ne_zero 2 hp.2.ne_zero):Matrix (Fin 2) (Fin 2) ℂ)=_
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [cubicThetaInversionMatrix,cubicThetaPrimeDilation,Matrix.mul_apply,Fin.sum_univ_two,
      ←pow_two,cubicThetaPrimeSquareRoot_sq]

lemma cubicThetaPrimeDoubleRootWeylPoint_involutive {p : Eisenstein} (hp : primaryPrime p)
    (y : CubicThetaPoint) :
    cubicThetaPrimeDoubleRootWeylElement hp • (cubicThetaPrimeDoubleRootWeylElement hp • y)=y := by
  apply Subtype.ext
  change cubicThetaMobius (cubicThetaPrimeDoubleRootWeylElement hp)
    (cubicThetaMobius (cubicThetaPrimeDoubleRootWeylElement hp) y.val)=y.val
  rw [cubicThetaPrimeDoubleRootWeylElement_inversion,
    cubicThetaMobius_inversion _ (cubicThetaMobius_height_pos _ y.property),
    cubicThetaMobius_inversion _ y.property]
  exact cubicThetaInversion_involutive
    (fun he => (pow_ne_zero 2 hp.2.ne_zero) (Subtype.ext he)) y.property

end CubicFirstMoment

end

end OAI
