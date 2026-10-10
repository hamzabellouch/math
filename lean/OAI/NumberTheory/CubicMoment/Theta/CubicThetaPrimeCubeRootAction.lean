import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeRootConjugation

namespace OAI

/-! The literal cubic-scale fractional root preserves the arithmetic
subgroup and its actual cubic multiplier. -/
noncomputable section
open scoped MatrixGroups
namespace CubicFirstMoment

def cubicThetaPrimeCubeRootElement {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) : SL(2,ℂ) :=
  (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero))⁻¹*
    cubicThetaPrincipalComplex (cubicThetaPrincipalTranslation x)*
      cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero)

theorem cubicThetaPrimeCubeRootElement_intertwines {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) (g : cubicThetaPrimeCubeRootSubgroup p) :
    cubicThetaPrimeCubeRootElement hp x*cubicThetaPrincipalComplex g.val=
      cubicThetaPrincipalComplex (cubicThetaPrimeCubeRootConjugate hp x g).val*
        cubicThetaPrimeCubeRootElement hp x := by
  let D := cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero)
  let t := cubicThetaPrincipalComplex (cubicThetaPrincipalTranslation x)
  let q := cubicThetaPrincipalComplex (cubicThetaPrimeConjugate (cubicThetaPrimeCube_primary hp)
    (cubicThetaPrimeCubeRootIwahori g))
  let q' := cubicThetaPrincipalComplex (cubicThetaPrimeConjugate (cubicThetaPrimeCube_primary hp)
    (cubicThetaPrimeCubeRootIwahori (cubicThetaPrimeCubeRootConjugate hp x g)))
  have hg : D*cubicThetaPrincipalComplex g.val=q*D :=
    cubicThetaPrimeDilation_intertwines (cubicThetaPrimeCube_primary hp) (cubicThetaPrimeCubeRootIwahori g)
  have hg' : D*cubicThetaPrincipalComplex (cubicThetaPrimeCubeRootConjugate hp x g).val=q'*D :=
    cubicThetaPrimeDilation_intertwines (cubicThetaPrimeCube_primary hp)
      (cubicThetaPrimeCubeRootIwahori (cubicThetaPrimeCubeRootConjugate hp x g))
  have hq : q'=t*q*t⁻¹ := by
    change cubicThetaPrincipalComplex _=_
    rw [cubicThetaPrimeCubeRootConjugate_dilation,map_mul,map_mul,map_inv]
  have ht : t*q=q'*t := by rw [hq]; group
  have hg'' : D⁻¹*q'*D=cubicThetaPrincipalComplex (cubicThetaPrimeCubeRootConjugate hp x g).val := by
    rw [mul_assoc,←hg']
    group
  change D⁻¹*t*D*cubicThetaPrincipalComplex g.val=
    cubicThetaPrincipalComplex (cubicThetaPrimeCubeRootConjugate hp x g).val*(D⁻¹*t*D)
  calc
    _ = D⁻¹*t*(D*cubicThetaPrincipalComplex g.val) := by group
    _ = D⁻¹*t*(q*D) := by rw [hg]
    _ = D⁻¹*(t*q)*D := by group
    _ = D⁻¹*(q'*t)*D := by rw [ht]
    _ = (D⁻¹*q'*D)*(D⁻¹*t*D) := by group
    _ = _ := by rw [hg'']

end CubicFirstMoment

end

end OAI
