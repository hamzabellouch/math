import OAI.NumberTheory.CubicMoment.Theta.CubicThetaProperAction
import Mathlib.Topology.Bases

namespace OAI

/-! The actual topological quotient by the principal level-three group.
Proper discontinuity supplies Hausdorffness; the open quotient map
preserves local compactness. -/
noncomputable section
namespace CubicFirstMoment

instance cubicThetaPoint_locallyCompact : LocallyCompactSpace CubicThetaPoint :=
  (isOpen_lt continuous_const continuous_snd : IsOpen {p : ℂ × ℝ | 0<p.2}).locallyCompactSpace

instance cubicThetaPrincipalPointAction_continuous :
    ContinuousConstSMul cubicThetaPrincipalGroup CubicThetaPoint where
  continuous_const_smul g := continuous_const_smul g.val

abbrev CubicThetaQuotient :=
  Quotient (MulAction.orbitRel cubicThetaPrincipalGroup CubicThetaPoint)

def cubicThetaQuotientMap : CubicThetaPoint → CubicThetaQuotient :=
  Quotient.mk (MulAction.orbitRel cubicThetaPrincipalGroup CubicThetaPoint)

lemma cubicThetaQuotientMap_open : IsOpenQuotientMap cubicThetaQuotientMap :=
  MulAction.isOpenQuotientMap_quotientMk

instance cubicThetaQuotient_t2 : T2Space CubicThetaQuotient := inferInstance

instance cubicThetaQuotient_locallyCompact : LocallyCompactSpace CubicThetaQuotient :=
  cubicThetaQuotientMap_open.locallyCompactSpace

instance cubicThetaQuotient_secondCountable : SecondCountableTopology CubicThetaQuotient :=
  Topology.IsOpenQuotientMap.secondCountableTopology cubicThetaQuotientMap_open

lemma cubicThetaQuotientMap_surjective : Function.Surjective cubicThetaQuotientMap :=
  Quotient.mk_surjective

end CubicFirstMoment

end

end OAI
