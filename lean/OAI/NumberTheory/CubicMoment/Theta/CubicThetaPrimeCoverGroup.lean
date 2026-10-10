import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeAtkinInvolution

namespace OAI

/-! The actual common finite arithmetic cover on which the prime
normalizer has the original cubic multiplier. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaPrimeCoverGroup {p : Eisenstein} (hp : primaryPrime p) :
    Subgroup cubicThetaPrincipalGroup :=
  (cubicThetaPrimeCharacterKernel hp).map (cubicThetaPrimeIwahori p).subtype

def cubicThetaPrimeCoverGroupEquiv {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaPrimeCharacterKernel hp ≃* cubicThetaPrimeCoverGroup hp :=
  (cubicThetaPrimeCharacterKernel hp).equivMapOfInjective
    (cubicThetaPrimeIwahori p).subtype (cubicThetaPrimeIwahori p).subtype_injective

instance cubicThetaPrimeCoverGroup_finiteIndex {p : Eisenstein} (hp : primaryPrime p) :
    (cubicThetaPrimeCoverGroup hp).FiniteIndex where
  index_ne_zero := by
    rw [cubicThetaPrimeCoverGroup,Subgroup.index_map_subtype]
    exact mul_ne_zero (cubicThetaPrimeCharacterKernel_finiteIndex hp).index_ne_zero
      (cubicThetaPrimeIwahori_finiteIndex hp.2.ne_zero).index_ne_zero

instance cubicThetaPrimeCoverGroup_continuous {p : Eisenstein} (hp : primaryPrime p) :
    ContinuousConstSMul (cubicThetaPrimeCoverGroup hp) CubicThetaPoint where
  continuous_const_smul g := continuous_const_smul g.val

abbrev CubicThetaPrimeCover {p : Eisenstein} (hp : primaryPrime p) :=
  Quotient (MulAction.orbitRel (cubicThetaPrimeCoverGroup hp) CubicThetaPoint)

def cubicThetaPrimeCoverMap {p : Eisenstein} (hp : primaryPrime p) :
    CubicThetaPoint → CubicThetaPrimeCover hp :=
  Quotient.mk (MulAction.orbitRel (cubicThetaPrimeCoverGroup hp) CubicThetaPoint)

lemma cubicThetaPrimeCoverMap_open {p : Eisenstein} (hp : primaryPrime p) :
    IsOpenQuotientMap (cubicThetaPrimeCoverMap hp) :=
  MulAction.isOpenQuotientMap_quotientMk

instance cubicThetaPrimeCover_t2 {p : Eisenstein} (hp : primaryPrime p) :
    T2Space (CubicThetaPrimeCover hp) := inferInstance

instance cubicThetaPrimeCover_locallyCompact {p : Eisenstein} (hp : primaryPrime p) :
    LocallyCompactSpace (CubicThetaPrimeCover hp) :=
  (cubicThetaPrimeCoverMap_open hp).locallyCompactSpace

instance cubicThetaPrimeCover_secondCountable {p : Eisenstein} (hp : primaryPrime p) :
    SecondCountableTopology (CubicThetaPrimeCover hp) :=
  Topology.IsOpenQuotientMap.secondCountableTopology (cubicThetaPrimeCoverMap_open hp)

lemma cubicThetaPrimeCover_covering {p : Eisenstein} (hp : primaryPrime p) :
    IsQuotientCoveringMap (cubicThetaPrimeCoverMap hp) (cubicThetaPrimeCoverGroup hp) :=
  isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul

def cubicThetaPrimeCoverProjection {p : Eisenstein} (hp : primaryPrime p) :
    CubicThetaPrimeCover hp → CubicThetaQuotient :=
  Quotient.map id (by
    intro a b hab
    obtain ⟨g,hg⟩ := hab
    exact ⟨g.val,hg⟩)

lemma cubicThetaPrimeCoverProjection_apply {p : Eisenstein} (hp : primaryPrime p)
    (x : CubicThetaPoint) :
    cubicThetaPrimeCoverProjection hp (cubicThetaPrimeCoverMap hp x)=cubicThetaQuotientMap x := rfl

lemma cubicThetaPrimeCoverProjection_continuous {p : Eisenstein} (hp : primaryPrime p) :
    Continuous (cubicThetaPrimeCoverProjection hp) := by
  apply (cubicThetaPrimeCoverMap_open hp).isQuotientMap.continuous_iff.mpr
  exact cubicThetaQuotientMap_open.continuous

end CubicFirstMoment

end

end OAI
