import OAI.NumberTheory.CubicMoment.Theta.CubicThetaEllipticTrace
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrincipalTrace
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaQuotient
import Mathlib.Topology.Covering.Quotient

namespace OAI

/-! The level-three quotient is a genuine covering: the actual principal
congruence action has no nontrivial point stabilizers. -/
noncomputable section
open scoped MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaPrincipalComplex_injective : Function.Injective cubicThetaPrincipalComplex := by
  intro g h he
  apply Subtype.ext
  apply Subtype.ext
  apply Matrix.ext
  intro i j
  apply Subtype.ext
  exact congrArg (fun k : SL(2,ℂ) => k i j) he

lemma cubicThetaPrincipal_fixed_eq_one (g : cubicThetaPrincipalGroup) (p : CubicThetaPoint)
    (hg : g • p=p) : g=1 := by
  have hp : cubicThetaMobius (cubicThetaPrincipalComplex g) p.val=p.val :=
    congrArg Subtype.val hg
  have ht := cubicThetaFixed_trace_norm p (cubicThetaPrincipalComplex g) hp
  have ht' := cubicThetaPrincipal_trace_eq_two_of_norm_le g (by
    simpa only [cubicThetaPrincipalComplex_apply,Subalgebra.coe_add] using ht)
  apply cubicThetaPrincipalComplex_injective
  rw [map_one]
  apply cubicThetaFixed_trace_two p _ hp
  change ((g.val 0 0:Eisenstein):ℂ)+((g.val 1 1:Eisenstein):ℂ)=2
  change ((g.val 0 0+g.val 1 1:Eisenstein):ℂ)=((2:Eisenstein):ℂ)
  exact congrArg Subtype.val ht'

instance cubicThetaPrincipalPointAction_free :
    IsCancelSMul cubicThetaPrincipalGroup CubicThetaPoint :=
  isCancelSMul_iff_eq_one_of_smul_eq.mpr cubicThetaPrincipal_fixed_eq_one

lemma cubicThetaQuotient_covering :
    IsQuotientCoveringMap cubicThetaQuotientMap cubicThetaPrincipalGroup :=
  isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul

lemma cubicThetaQuotient_localHomeomorph : IsLocalHomeomorph cubicThetaQuotientMap :=
  cubicThetaQuotient_covering.isCoveringMap.isLocalHomeomorph

end CubicFirstMoment

end

end OAI
