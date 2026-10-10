import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeRootTranslation
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFreeAction

namespace OAI

/-! The fractional roots normalize the actual arithmetic subgroup. The
inverse is the negative root, with no choice of an abstract local model. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeRootConjugate_complex {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) (g : cubicThetaPrimeCubeRootSubgroup p) :
    cubicThetaPrincipalComplex (cubicThetaPrimeCubeRootConjugate hp x g).val=
      cubicThetaPrimeCubeRootElement hp x*cubicThetaPrincipalComplex g.val*
        (cubicThetaPrimeCubeRootElement hp x)⁻¹ := by
  rw [eq_mul_inv_iff_mul_eq]
  exact (cubicThetaPrimeCubeRootElement_intertwines hp x g).symm

lemma cubicThetaPrimeCubeRootConjugate_add {p : Eisenstein} (hp : primaryPrime p)
    (x y : Eisenstein) (g : cubicThetaPrimeCubeRootSubgroup p) :
    cubicThetaPrimeCubeRootConjugate hp (x+y) g=
      cubicThetaPrimeCubeRootConjugate hp x (cubicThetaPrimeCubeRootConjugate hp y g) := by
  apply Subtype.ext
  apply cubicThetaPrincipalComplex_injective
  simp only [cubicThetaPrimeCubeRootConjugate_complex,cubicThetaPrimeCubeRootElement_add,mul_inv_rev]
  group

@[simp] lemma cubicThetaPrimeCubeRootConjugate_zero {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeCubeRootSubgroup p) : cubicThetaPrimeCubeRootConjugate hp 0 g=g := by
  apply Subtype.ext
  apply cubicThetaPrincipalComplex_injective
  simp only [cubicThetaPrimeCubeRootConjugate_complex,cubicThetaPrimeCubeRootElement_zero,
    one_mul,inv_one,mul_one]

def cubicThetaPrimeCubeRootAutomorphism {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) : cubicThetaPrimeCubeRootSubgroup p ≃* cubicThetaPrimeCubeRootSubgroup p where
  toFun := cubicThetaPrimeCubeRootConjugate hp x
  invFun := cubicThetaPrimeCubeRootConjugate hp (-x)
  left_inv g := by
    rw [←cubicThetaPrimeCubeRootConjugate_add,neg_add_cancel,cubicThetaPrimeCubeRootConjugate_zero]
  right_inv g := by
    rw [←cubicThetaPrimeCubeRootConjugate_add,add_neg_cancel,cubicThetaPrimeCubeRootConjugate_zero]
  map_mul' g h := by
    apply Subtype.ext
    apply cubicThetaPrincipalComplex_injective
    change cubicThetaPrincipalComplex (cubicThetaPrimeCubeRootConjugate hp x (g*h)).val=
      cubicThetaPrincipalComplex ((cubicThetaPrimeCubeRootConjugate hp x g).val*
        (cubicThetaPrimeCubeRootConjugate hp x h).val)
    simp only [cubicThetaPrimeCubeRootConjugate_complex,map_mul,Subgroup.coe_mul]
    group

end CubicFirstMoment

end

end OAI
