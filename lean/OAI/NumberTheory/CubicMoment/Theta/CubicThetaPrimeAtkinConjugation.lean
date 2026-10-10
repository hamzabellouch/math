import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCharacterAverage
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaInversionCharacter

namespace OAI

/-! The prime Atkin involution on the actual arithmetic subgroup. Its
cubic twist disappears on the kernel of the diagonal character. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaPrimeAtkinConjugate {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeIwahori p) : cubicThetaPrimeIwahori p :=
  ⟨cubicThetaPrincipalConjugate cubicThetaFullInversion⁻¹
      (cubicThetaPrimeConjugate hp.1 g),by
    have he := (cubicThetaInversionConjugate_entries (cubicThetaPrimeConjugate hp.1 g)).2
    change p∣(cubicThetaPrincipalConjugate cubicThetaFullInversion⁻¹
      (cubicThetaPrimeConjugate hp.1 g)).val 1 0
    rw [he]
    change p∣-(p*g.val.val 0 1)
    exact dvd_neg.mpr (dvd_mul_right p _)⟩

lemma cubicThetaPrimeAtkinConjugate_diagonal {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeIwahori p) :
    (cubicThetaPrimeAtkinConjugate hp g).val.val 0 0=g.val.val 1 1 := by
  exact (cubicThetaInversionConjugate_entries (cubicThetaPrimeConjugate hp.1 g)).1

lemma cubicThetaPrimeAtkinConjugate_character_product {p : Eisenstein}
    (hp : primaryPrime p) (g : cubicThetaPrimeIwahori p) :
    cubicThetaPrimeIwahoriCharacter p hp g*
      cubicThetaPrimeIwahoriCharacter p hp (cubicThetaPrimeAtkinConjugate hp g)=1 := by
  change cubicSymbol p (g.val.val 0 0)*
    cubicSymbol p ((cubicThetaPrimeAtkinConjugate hp g).val.val 0 0)=1
  rw [cubicThetaPrimeAtkinConjugate_diagonal,←cubicSymbol_mul_upper hp.1]
  have hd : p∣g.val.val 0 0*g.val.val 1 1-1 := by
    rw [show g.val.val 0 0*g.val.val 1 1-1=g.val.val 0 1*g.val.val 1 0 by
      linear_combination cubicThetaPrincipalGroup_det g.val]
    exact dvd_mul_of_dvd_right g.property _
  rw [cubicSymbol_congr (residue_eq_of_dvd_sub hd)]
  simpa only [pow_zero] using cubicSymbol_pow_upper hp.1 1 0

def cubicThetaPrimeCharacterKernel {p : Eisenstein} (hp : primaryPrime p) :
    Subgroup (cubicThetaPrimeIwahori p) := (cubicThetaPrimeIwahoriCharacter p hp).ker

theorem cubicThetaPrimeCharacterKernel_finiteIndex {p : Eisenstein}
    (hp : primaryPrime p) : (cubicThetaPrimeCharacterKernel hp).FiniteIndex := by
  let : Finite (Residues p) := finite_residues hp.2.ne_zero
  let : Finite (cubicThetaPrimeIwahoriDiagonal hp).range := inferInstance
  let : (cubicThetaPrimeIwahoriDiagonal hp).ker.FiniteIndex := inferInstance
  have hle : (cubicThetaPrimeIwahoriDiagonal hp).ker≤cubicThetaPrimeCharacterKernel hp := by
    intro g hg
    change cubicThetaPrimeIwahoriDiagonal hp g=1 at hg
    change cubicThetaPrimeIwahoriCharacter p hp g=1
    rw [cubicThetaPrimeIwahoriCharacter_diagonal,hg,Units.val_one,map_one]
  exact Subgroup.finiteIndex_of_le hle

def cubicThetaPrimeAtkinKernel {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeCharacterKernel hp) : cubicThetaPrimeCharacterKernel hp :=
  ⟨cubicThetaPrimeAtkinConjugate hp g.val,by
    have he := cubicThetaPrimeAtkinConjugate_character_product hp g.val
    have hg : cubicThetaPrimeIwahoriCharacter p hp g.val=1 := g.property
    rw [hg,one_mul] at he
    exact he⟩

lemma cubicThetaPrimeAtkinKernel_kubota {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeCharacterKernel hp) :
    cubicThetaKubotaValue (cubicThetaPrimeAtkinKernel hp g).val.val=
      cubicThetaKubotaValue g.val.val := by
  change cubicThetaKubotaValue (cubicThetaPrincipalConjugate cubicThetaFullInversion⁻¹
    (cubicThetaPrimeConjugate hp.1 g.val))=cubicThetaKubotaValue g.val.val
  rw [cubicThetaInversionConjugate_character]
  have he := cubicThetaPrimeConjugate_kubota hp g.val
  have hg : cubicThetaPrimeIwahoriCharacter p hp g.val=1 := g.property
  rw [hg,one_mul] at he
  exact he.symm

end CubicFirstMoment

end

end OAI
