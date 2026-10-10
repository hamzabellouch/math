import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeRootTranslation
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFreeAction

namespace OAI

/-! The fractional roots normalize the actual arithmetic subgroup. The
inverse is the negative root, with no choice of an abstract local model. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPrimeRootConjugate_complex {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) (g : cubicThetaPrimeRootSubgroup p) :
    cubicThetaPrincipalComplex (cubicThetaPrimeRootConjugate hp x g).val=
      cubicThetaPrimeRootElement hp x*cubicThetaPrincipalComplex g.val*
        (cubicThetaPrimeRootElement hp x)⁻¹ := by
  rw [eq_mul_inv_iff_mul_eq]
  exact (cubicThetaPrimeRootElement_intertwines hp x g).symm

lemma cubicThetaPrimeRootConjugate_add {p : Eisenstein} (hp : primaryPrime p)
    (x y : Eisenstein) (g : cubicThetaPrimeRootSubgroup p) :
    cubicThetaPrimeRootConjugate hp (x+y) g=
      cubicThetaPrimeRootConjugate hp x (cubicThetaPrimeRootConjugate hp y g) := by
  apply Subtype.ext
  apply cubicThetaPrincipalComplex_injective
  simp only [cubicThetaPrimeRootConjugate_complex,cubicThetaPrimeRootElement_add,mul_inv_rev]
  group

@[simp] lemma cubicThetaPrimeRootConjugate_zero {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeRootSubgroup p) : cubicThetaPrimeRootConjugate hp 0 g=g := by
  apply Subtype.ext
  apply cubicThetaPrincipalComplex_injective
  simp only [cubicThetaPrimeRootConjugate_complex,cubicThetaPrimeRootElement_zero,
    one_mul,inv_one,mul_one]

def cubicThetaPrimeRootAutomorphism {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) : cubicThetaPrimeRootSubgroup p ≃* cubicThetaPrimeRootSubgroup p where
  toFun := cubicThetaPrimeRootConjugate hp x
  invFun := cubicThetaPrimeRootConjugate hp (-x)
  left_inv g := by
    rw [←cubicThetaPrimeRootConjugate_add,neg_add_cancel,cubicThetaPrimeRootConjugate_zero]
  right_inv g := by
    rw [←cubicThetaPrimeRootConjugate_add,add_neg_cancel,cubicThetaPrimeRootConjugate_zero]
  map_mul' g h := by
    apply Subtype.ext
    apply cubicThetaPrincipalComplex_injective
    change cubicThetaPrincipalComplex (cubicThetaPrimeRootConjugate hp x (g*h)).val=
      cubicThetaPrincipalComplex ((cubicThetaPrimeRootConjugate hp x g).val*
        (cubicThetaPrimeRootConjugate hp x h).val)
    simp only [cubicThetaPrimeRootConjugate_complex,map_mul,Subgroup.coe_mul]
    group

end CubicFirstMoment

end

end OAI
