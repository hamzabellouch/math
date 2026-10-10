import OAI.NumberTheory.CubicMoment.Theta.CubicThetaArithmeticResolvent

namespace OAI

/-! The continued family tested against actual compact automorphic
sections. On the initial half-plane these are the literal quotient
integrals of the arithmetic Eisenstein remainder. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

def cubicThetaArithmeticDistribution (F : CubicThetaSection)
    (hc : HasCompactSupport (cubicThetaSectionNorm F)) (s : ℂ) : ℂ :=
  inner ℂ ((cubicThetaCompactSection_memLp F hc).toLp _) (cubicThetaForcedResolvent s)

theorem cubicThetaArithmeticDistribution_meromorphic (F : CubicThetaSection)
    (hc : HasCompactSupport (cubicThetaSectionNorm F)) {s : ℂ} (hs : 1<s.re) :
    MeromorphicAt (cubicThetaArithmeticDistribution F hc) s :=
  cubicThetaMeromorphic_clm (innerSL ℂ ((cubicThetaCompactSection_memLp F hc).toLp _))
    (cubicThetaForcedResolvent_meromorphic hs)

lemma cubicThetaArithmeticDistribution_right (F : CubicThetaSection)
    (hc : HasCompactSupport (cubicThetaSectionNorm F)) {s : ℂ} (hs : 3<s.re) :
    cubicThetaArithmeticDistribution F hc s=
      ∫ q, cubicThetaSectionPairing F (cubicThetaArithmeticSection s (by linarith)) q
        ∂cubicThetaQuotientMeasure := by
  unfold cubicThetaArithmeticDistribution
  rw [← cubicThetaArithmeticL2_eq_forcedResolvent hs]
  exact cubicThetaSectionPairing_L2 F _ (cubicThetaCompactSection_memLp F hc)
    (cubicThetaArithmeticSection_memLp hs)

lemma cubicThetaArithmeticDistribution_chart_right {s : ℂ} (hs : 3<s.re)
    {g : ℂ × ℝ → ℂ} (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g)
    {K : Set (ℂ × ℝ)} (hK : IsCompact K) (hp : K⊆{y : ℂ × ℝ | 0<y.2})
    (hgs : tsupport g⊆K)
    (e : OpenPartialHomeomorph CubicThetaPoint CubicThetaQuotient)
    (he : (e : CubicThetaPoint → CubicThetaQuotient)=cubicThetaQuotientMap)
    (hKe : cubicThetaPointInclusion.symm '' K⊆e.source) :
    let P := cubicThetaPoincareSection (cubicThetaCoordinateSeed g hg.continuous hc (hgs.trans hp))
    cubicThetaArithmeticDistribution P (cubicThetaPoincareSection_compact _) s=
      ∫ y in K, star (g y)*cubicThetaArithmeticRemainder y s/(y.2:ℂ)^3 := by
  intro P
  rw [cubicThetaArithmeticDistribution_right P _ hs,
    cubicThetaCoordinateSection_mass_pairing hg hc hK hp hgs e he hKe]
  apply setIntegral_congr_fun hK.measurableSet
  intro y hy
  dsimp only
  rw [cubicThetaSectionFunction_apply _ (hp hy)]
  rfl

end CubicFirstMoment

end

end OAI
