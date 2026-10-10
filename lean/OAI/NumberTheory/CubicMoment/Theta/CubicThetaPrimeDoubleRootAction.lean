import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeDoubleRootConjugation

namespace OAI

/-! The literal square-scale fractional root preserves the arithmetic
subgroup and its actual cubic multiplier. -/
noncomputable section
open scoped MatrixGroups
namespace CubicFirstMoment

def cubicThetaPrimeDoubleRootElement {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) : SL(2,ℂ) :=
  (cubicThetaPrimeDilation (pow_ne_zero 2 hp.2.ne_zero))⁻¹*
    cubicThetaPrincipalComplex (cubicThetaPrincipalTranslation x)*
      cubicThetaPrimeDilation (pow_ne_zero 2 hp.2.ne_zero)

theorem cubicThetaPrimeDoubleRootElement_intertwines {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) (g : cubicThetaPrimeDoubleRootSubgroup p) :
    cubicThetaPrimeDoubleRootElement hp x*cubicThetaPrincipalComplex g.val=
      cubicThetaPrincipalComplex (cubicThetaPrimeDoubleRootConjugate hp x g).val*
        cubicThetaPrimeDoubleRootElement hp x := by
  let D := cubicThetaPrimeDilation (pow_ne_zero 2 hp.2.ne_zero)
  let t := cubicThetaPrincipalComplex (cubicThetaPrincipalTranslation x)
  let q := cubicThetaPrincipalComplex (cubicThetaPrimeConjugate (cubicThetaPrimeDouble_primary hp)
    (cubicThetaPrimeDoubleRootIwahori g))
  let q' := cubicThetaPrincipalComplex (cubicThetaPrimeConjugate (cubicThetaPrimeDouble_primary hp)
    (cubicThetaPrimeDoubleRootIwahori (cubicThetaPrimeDoubleRootConjugate hp x g)))
  have hg : D*cubicThetaPrincipalComplex g.val=q*D :=
    cubicThetaPrimeDilation_intertwines (cubicThetaPrimeDouble_primary hp) (cubicThetaPrimeDoubleRootIwahori g)
  have hg' : D*cubicThetaPrincipalComplex (cubicThetaPrimeDoubleRootConjugate hp x g).val=q'*D :=
    cubicThetaPrimeDilation_intertwines (cubicThetaPrimeDouble_primary hp)
      (cubicThetaPrimeDoubleRootIwahori (cubicThetaPrimeDoubleRootConjugate hp x g))
  have hq : q'=t*q*t⁻¹ := by
    change cubicThetaPrincipalComplex _=_
    rw [cubicThetaPrimeDoubleRootConjugate_dilation,map_mul,map_mul,map_inv]
  have ht : t*q=q'*t := by rw [hq]; group
  have hg'' : D⁻¹*q'*D=cubicThetaPrincipalComplex (cubicThetaPrimeDoubleRootConjugate hp x g).val := by
    rw [mul_assoc,←hg']
    group
  change D⁻¹*t*D*cubicThetaPrincipalComplex g.val=
    cubicThetaPrincipalComplex (cubicThetaPrimeDoubleRootConjugate hp x g).val*(D⁻¹*t*D)
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
