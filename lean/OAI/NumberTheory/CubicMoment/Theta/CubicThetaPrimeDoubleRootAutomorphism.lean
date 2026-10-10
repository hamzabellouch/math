import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeDoubleRootTranslation
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFreeAction

namespace OAI

/-! The fractional roots normalize the actual arithmetic subgroup. The
inverse is the negative root, with no choice of an abstract local model. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPrimeDoubleRootConjugate_complex {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) (g : cubicThetaPrimeDoubleRootSubgroup p) :
    cubicThetaPrincipalComplex (cubicThetaPrimeDoubleRootConjugate hp x g).val=
      cubicThetaPrimeDoubleRootElement hp x*cubicThetaPrincipalComplex g.val*
        (cubicThetaPrimeDoubleRootElement hp x)⁻¹ := by
  rw [eq_mul_inv_iff_mul_eq]
  exact (cubicThetaPrimeDoubleRootElement_intertwines hp x g).symm

lemma cubicThetaPrimeDoubleRootConjugate_add {p : Eisenstein} (hp : primaryPrime p)
    (x y : Eisenstein) (g : cubicThetaPrimeDoubleRootSubgroup p) :
    cubicThetaPrimeDoubleRootConjugate hp (x+y) g=
      cubicThetaPrimeDoubleRootConjugate hp x (cubicThetaPrimeDoubleRootConjugate hp y g) := by
  apply Subtype.ext
  apply cubicThetaPrincipalComplex_injective
  simp only [cubicThetaPrimeDoubleRootConjugate_complex,cubicThetaPrimeDoubleRootElement_add,mul_inv_rev]
  group

@[simp] lemma cubicThetaPrimeDoubleRootConjugate_zero {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeDoubleRootSubgroup p) : cubicThetaPrimeDoubleRootConjugate hp 0 g=g := by
  apply Subtype.ext
  apply cubicThetaPrincipalComplex_injective
  simp only [cubicThetaPrimeDoubleRootConjugate_complex,cubicThetaPrimeDoubleRootElement_zero,
    one_mul,inv_one,mul_one]

def cubicThetaPrimeDoubleRootAutomorphism {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) : cubicThetaPrimeDoubleRootSubgroup p ≃* cubicThetaPrimeDoubleRootSubgroup p where
  toFun := cubicThetaPrimeDoubleRootConjugate hp x
  invFun := cubicThetaPrimeDoubleRootConjugate hp (-x)
  left_inv g := by
    rw [←cubicThetaPrimeDoubleRootConjugate_add,neg_add_cancel,cubicThetaPrimeDoubleRootConjugate_zero]
  right_inv g := by
    rw [←cubicThetaPrimeDoubleRootConjugate_add,add_neg_cancel,cubicThetaPrimeDoubleRootConjugate_zero]
  map_mul' g h := by
    apply Subtype.ext
    apply cubicThetaPrincipalComplex_injective
    change cubicThetaPrincipalComplex (cubicThetaPrimeDoubleRootConjugate hp x (g*h)).val=
      cubicThetaPrincipalComplex ((cubicThetaPrimeDoubleRootConjugate hp x g).val*
        (cubicThetaPrimeDoubleRootConjugate hp x h).val)
    simp only [cubicThetaPrimeDoubleRootConjugate_complex,map_mul,Subgroup.coe_mul]
    group

end CubicFirstMoment

end

end OAI
