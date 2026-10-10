import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeRootCharacter
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeDilation

namespace OAI

/-! The actual complex root element acts on the arithmetic subgroup with
its original cubic multiplier. -/
noncomputable section
open scoped MatrixGroups
namespace CubicFirstMoment

def cubicThetaPrimeRootElement {p : Eisenstein} (hp : primaryPrime p) (x : Eisenstein) : SL(2,ℂ) :=
  (cubicThetaPrimeDilation hp.2.ne_zero)⁻¹*cubicThetaPrincipalComplex (cubicThetaPrincipalTranslation x)*
    cubicThetaPrimeDilation hp.2.ne_zero

theorem cubicThetaPrimeRootElement_intertwines {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) (g : cubicThetaPrimeRootSubgroup p) :
    cubicThetaPrimeRootElement hp x*cubicThetaPrincipalComplex g.val=
      cubicThetaPrincipalComplex (cubicThetaPrimeRootConjugate hp x g).val*
        cubicThetaPrimeRootElement hp x := by
  let D := cubicThetaPrimeDilation hp.2.ne_zero
  let t := cubicThetaPrincipalComplex (cubicThetaPrincipalTranslation x)
  let q := cubicThetaPrincipalComplex (cubicThetaPrimeConjugate hp.1 (cubicThetaPrimeRootIwahori g))
  let q' := cubicThetaPrincipalComplex (cubicThetaPrimeConjugate hp.1
    (cubicThetaPrimeRootIwahori (cubicThetaPrimeRootConjugate hp x g)))
  have hg : D*cubicThetaPrincipalComplex g.val=q*D :=
    cubicThetaPrimeDilation_intertwines hp.1 (cubicThetaPrimeRootIwahori g)
  have hg' : D*cubicThetaPrincipalComplex (cubicThetaPrimeRootConjugate hp x g).val=q'*D :=
    cubicThetaPrimeDilation_intertwines hp.1 (cubicThetaPrimeRootIwahori (cubicThetaPrimeRootConjugate hp x g))
  have hq : q'=t*q*t⁻¹ := by
    change cubicThetaPrincipalComplex _=_
    rw [cubicThetaPrimeRootConjugate_dilation,map_mul,map_mul,map_inv]
  have ht : t*q=q'*t := by rw [hq]; group
  have hg'' : D⁻¹*q'*D=cubicThetaPrincipalComplex (cubicThetaPrimeRootConjugate hp x g).val := by
    rw [mul_assoc,←hg']
    group
  change D⁻¹*t*D*cubicThetaPrincipalComplex g.val=
    cubicThetaPrincipalComplex (cubicThetaPrimeRootConjugate hp x g).val*(D⁻¹*t*D)
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
