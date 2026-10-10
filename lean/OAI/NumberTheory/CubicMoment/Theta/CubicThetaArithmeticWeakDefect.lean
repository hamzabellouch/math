import OAI.NumberTheory.CubicMoment.Theta.CubicThetaArithmeticChartWeak
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaArithmeticEnergyGraph
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaC1PairingIntegral
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaC1EnergyNorm
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaForcingL2

namespace OAI

/-! A continuous additive defect for the literal arithmetic weak
PDE. Its vanishing can be glued and passed to the energy completion. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

def cubicThetaArithmeticWeakDefect (s : ℂ) (hs : 3<s.re) :
    CubicThetaGlobalEnergyAmbient →+ ℂ where
  toFun u :=
    inner ℂ (WithLp.sndL 2 ℂ CubicThetaGlobalL2 CubicThetaGradientL2 u)
      (cubicThetaArithmeticGradientL2 s hs)+
    s*(s-2)*inner ℂ (WithLp.fstL 2 ℂ CubicThetaGlobalL2 CubicThetaGradientL2 u)
      (cubicThetaArithmeticL2 s hs)-
    inner ℂ (WithLp.fstL 2 ℂ CubicThetaGlobalL2 CubicThetaGradientL2 u)
      (cubicThetaForcingL2 s)
  map_zero' := by simp
  map_add' u v := by
    simp only [map_add,inner_add_left]
    ring

lemma cubicThetaArithmeticWeakDefect_continuous (s : ℂ) (hs : 3<s.re) :
    Continuous (cubicThetaArithmeticWeakDefect s hs) := by
  change Continuous (fun u : CubicThetaGlobalEnergyAmbient =>
    inner ℂ (WithLp.sndL 2 ℂ CubicThetaGlobalL2 CubicThetaGradientL2 u)
      (cubicThetaArithmeticGradientL2 s hs)+
    s*(s-2)*inner ℂ (WithLp.fstL 2 ℂ CubicThetaGlobalL2 CubicThetaGradientL2 u)
      (cubicThetaArithmeticL2 s hs)-
    inner ℂ (WithLp.fstL 2 ℂ CubicThetaGlobalL2 CubicThetaGradientL2 u)
      (cubicThetaForcingL2 s))
  fun_prop

lemma cubicThetaArithmeticWeakDefect_C1 (s : ℂ) (hs : 3<s.re)
    (F : CubicThetaSection)
    (hF : ContDiffOn ℝ 1 (cubicThetaSectionFunction F) {y : ℂ × ℝ | 0<y.2})
    (hc : HasCompactSupport (cubicThetaSectionNorm F)) :
    cubicThetaArithmeticWeakDefect s hs (cubicThetaC1EnergyData F hF hc)=
      (∫ q, cubicThetaC1Pairing F (cubicThetaArithmeticSection s (by linarith)) q
        ∂cubicThetaQuotientMeasure)+
      s*(s-2)*(∫ q, cubicThetaSectionPairing F (cubicThetaArithmeticSection s (by linarith)) q
        ∂cubicThetaQuotientMeasure)-
      ∫ q, cubicThetaSectionPairing F (cubicThetaForcingSection s) q ∂cubicThetaQuotientMeasure := by
  change inner ℂ ((cubicThetaC1Gradient_memLp F hF hc).toLp _)
      ((cubicThetaArithmeticGradientRepresentative_memLp hs).toLp _)+
    s*(s-2)*inner ℂ ((cubicThetaCompactSection_memLp F hc).toLp _)
      ((cubicThetaArithmeticSection_memLp hs).toLp _)-
    inner ℂ ((cubicThetaCompactSection_memLp F hc).toLp _)
      ((cubicThetaSectionRepresentative_memLp (cubicThetaForcingTest s)).toLp _)=_
  rw [cubicThetaC1Pairing_L2 F _ hF (cubicThetaArithmeticSectionFunction_contDiffOn_one (by linarith)),
    cubicThetaSectionPairing_L2,cubicThetaSectionPairing_L2]
  rfl

lemma cubicThetaArithmeticWeakDefect_coordinate {s : ℂ} (hs : 3<s.re)
    {g : ℂ × ℝ → ℂ} (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g)
    {K : Set (ℂ × ℝ)} (hK : IsCompact K) (hp : K⊆{y : ℂ × ℝ | 0<y.2})
    (hgs : tsupport g⊆K)
    (e : OpenPartialHomeomorph CubicThetaPoint CubicThetaQuotient)
    (he : (e : CubicThetaPoint → CubicThetaQuotient)=cubicThetaQuotientMap)
    (hKe : cubicThetaPointInclusion.symm '' K⊆e.source) :
    cubicThetaArithmeticWeakDefect s hs (cubicThetaCoordinateData hg hc (hgs.trans hp))=0 := by
  rw [cubicThetaCoordinateData,cubicThetaArithmeticWeakDefect_C1]
  exact sub_eq_zero.mpr (cubicThetaArithmetic_chart_weak (by linarith) hg hc hK hp hgs e he hKe)

end CubicFirstMoment

end

end OAI
