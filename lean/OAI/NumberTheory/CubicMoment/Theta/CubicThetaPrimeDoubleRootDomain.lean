import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFiniteCoverIntegral
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeDoubleRootWeylSections
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeDoubleRootAutomorphism

namespace OAI

/-! The exact intermediate root cover and its two measure-preserving
root operations. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

def cubicThetaDoubleRootCover {p : Eisenstein} (hp : primaryPrime p) : CubicThetaArithmeticCover := by
  letI := cubicThetaPrimeDoubleRootSubgroup_finiteIndex hp
  exact cubicThetaRelativeCover cubicThetaBaseCover (cubicThetaPrimeDoubleRootSubgroup p) (le_top)

def cubicThetaPrimeDoubleRootDomain {p : Eisenstein} (hp : primaryPrime p) : Set CubicThetaPoint :=
  (cubicThetaDoubleRootCover hp).domain

lemma cubicThetaPrimeDoubleRootDomain_fundamental {p : Eisenstein} (hp : primaryPrime p) :
    IsFundamentalDomain (cubicThetaPrimeDoubleRootSubgroup p)
      (cubicThetaPrimeDoubleRootDomain hp) cubicThetaPointMeasure :=
  (cubicThetaDoubleRootCover hp).fundamental cubicThetaPointMeasure

lemma cubicThetaPrimeDoubleRootImage_fundamental {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) :
    IsFundamentalDomain (cubicThetaPrimeDoubleRootSubgroup p)
      ((fun z : CubicThetaPoint => cubicThetaPrimeDoubleRootElement hp x • z) ''
        cubicThetaPrimeDoubleRootDomain hp) cubicThetaPointMeasure := by
  apply (cubicThetaPrimeDoubleRootDomain_fundamental hp).image_of_equiv
    (Homeomorph.smul (cubicThetaPrimeDoubleRootElement hp x)).toEquiv
    (measurePreserving_smul (cubicThetaPrimeDoubleRootElement hp x)⁻¹
      cubicThetaPointMeasure).quasiMeasurePreserving
    (cubicThetaPrimeDoubleRootAutomorphism hp (-x)).toEquiv
  intro g y
  change cubicThetaPrimeDoubleRootElement hp x • ((cubicThetaPrimeDoubleRootConjugate hp (-x) g).val • y)=
    g.val • (cubicThetaPrimeDoubleRootElement hp x • y)
  rw [cubicThetaPrimeDoubleRootPoint_intertwines,←cubicThetaPrimeDoubleRootConjugate_add,
    add_neg_cancel,cubicThetaPrimeDoubleRootConjugate_zero]

lemma cubicThetaPrimeDoubleRootWeylImage_fundamental {p : Eisenstein} (hp : primaryPrime p) :
    IsFundamentalDomain (cubicThetaPrimeDoubleRootSubgroup p)
      ((fun z : CubicThetaPoint => cubicThetaPrimeDoubleRootWeylElement hp • z) ''
        cubicThetaPrimeDoubleRootDomain hp) cubicThetaPointMeasure := by
  apply (cubicThetaPrimeDoubleRootDomain_fundamental hp).image_of_equiv
    (Homeomorph.smul (cubicThetaPrimeDoubleRootWeylElement hp)).toEquiv
    (measurePreserving_smul (cubicThetaPrimeDoubleRootWeylElement hp)⁻¹
      cubicThetaPointMeasure).quasiMeasurePreserving
    (cubicThetaPrimeDoubleRootWeylConjugate_involutive hp).toPerm
  intro g y
  change cubicThetaPrimeDoubleRootWeylElement hp • ((cubicThetaPrimeDoubleRootWeylConjugate hp g).val • y)=
    g.val • (cubicThetaPrimeDoubleRootWeylElement hp • y)
  rw [cubicThetaPrimeDoubleRootWeylPoint_intertwines,cubicThetaPrimeDoubleRootWeylConjugate_involutive]

lemma cubicThetaPrimeDoubleRootIwahoriImage_fundamental {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeIwahori (p^2)) :
    IsFundamentalDomain (cubicThetaPrimeDoubleRootSubgroup p)
      ((fun z : CubicThetaPoint => g.val • z) '' cubicThetaPrimeDoubleRootDomain hp)
        cubicThetaPointMeasure := by
  apply (cubicThetaPrimeDoubleRootDomain_fundamental hp).image_of_equiv
    (Homeomorph.smul g.val).toEquiv
    (measurePreserving_smul g.val⁻¹ cubicThetaPointMeasure).quasiMeasurePreserving
    (cubicThetaPrimeRootIwahoriEquiv g⁻¹)
  intro h x
  change g.val • ((g.val⁻¹*h.val*(g.val⁻¹)⁻¹) • x)=h.val • (g.val • x)
  simp only [←mul_smul,inv_inv,mul_inv_cancel_left,mul_assoc]

end CubicFirstMoment

end

end OAI
