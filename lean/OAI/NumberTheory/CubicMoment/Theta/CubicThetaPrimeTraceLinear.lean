import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeTraceFiniteEnergy

namespace OAI

/-! Linearity of the literal finite trace, retaining its actual
finite-energy section before passing to the completion. -/
noncomputable section
namespace CubicFirstMoment

local instance primeTraceLinear_fintype {p : Eisenstein} (hp : primaryPrime p) :
    Fintype (cubicThetaPrimeTransversal hp) := Fintype.ofFinite _

lemma cubicThetaPrimeTraceSection_add {p : Eisenstein} (hp : primaryPrime p)
    (F G : cubicThetaPrimeSections hp) :
    cubicThetaPrimeTraceSection hp (F+G)=cubicThetaPrimeTraceSection hp F+cubicThetaPrimeTraceSection hp G := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro x
  change (∑ t : cubicThetaPrimeTransversal hp,
    star (cubicThetaKubotaValue t.val)*(F.val (t.val • x)+G.val (t.val • x)))=_
  simp only [mul_add,Finset.sum_add_distrib]
  rfl

lemma cubicThetaPrimeTraceSection_smul {p : Eisenstein} (hp : primaryPrime p)
    (c : ℂ) (F : cubicThetaPrimeSections hp) :
    cubicThetaPrimeTraceSection hp (c • F)=c • cubicThetaPrimeTraceSection hp F := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro x
  change (∑ t : cubicThetaPrimeTransversal hp,
    star (cubicThetaKubotaValue t.val)*(c*F.val (t.val • x)))=
      c*(∑ t : cubicThetaPrimeTransversal hp,star (cubicThetaKubotaValue t.val)*F.val (t.val • x))
  simp only [mul_left_comm,Finset.mul_sum]

def cubicThetaPrimeTraceFiniteLinear {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaPrimeFiniteEnergy hp →ₗ[ℂ] cubicThetaFiniteEnergySections where
  toFun := cubicThetaPrimeTraceFiniteEnergy hp
  map_add' F G := by
    apply Subtype.ext
    exact cubicThetaPrimeTraceSection_add hp F.val.val G.val.val
  map_smul' c F := by
    apply Subtype.ext
    exact cubicThetaPrimeTraceSection_smul hp c F.val.val

end CubicFirstMoment

end

end OAI
