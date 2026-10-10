import OAI.NumberTheory.CubicMoment.Theta.CubicThetaSmoothChartWeak
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaArithmeticGlobalWeak

namespace OAI

/-! A continuous weak defect for an actual smooth section and its
compact forcing. This will pass the coordinate equation to the energy closure. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

def cubicThetaSmoothWeakDefect (G : cubicThetaSmoothTests) (J : CubicThetaSection)
    (hJ : HasCompactSupport (cubicThetaSectionNorm J)) (lam : ℂ) :
    CubicThetaGlobalEnergyAmbient →+ ℂ where
  toFun u :=
    inner ℂ (WithLp.sndL 2 ℂ CubicThetaGlobalL2 CubicThetaGradientL2 u) (cubicThetaGlobalGradient G)+
    lam*inner ℂ (WithLp.fstL 2 ℂ CubicThetaGlobalL2 CubicThetaGradientL2 u) (cubicThetaGlobalMass G)-
    inner ℂ (WithLp.fstL 2 ℂ CubicThetaGlobalL2 CubicThetaGradientL2 u)
      ((cubicThetaCompactSection_memLp J hJ).toLp _)
  map_zero' := by simp
  map_add' u v := by
    simp only [map_add,inner_add_left]
    ring

lemma cubicThetaSmoothWeakDefect_continuous (G : cubicThetaSmoothTests) (J : CubicThetaSection)
    (hJ : HasCompactSupport (cubicThetaSectionNorm J)) (lam : ℂ) :
    Continuous (cubicThetaSmoothWeakDefect G J hJ lam) := by
  change Continuous (fun u : CubicThetaGlobalEnergyAmbient =>
    inner ℂ (WithLp.sndL 2 ℂ CubicThetaGlobalL2 CubicThetaGradientL2 u) (cubicThetaGlobalGradient G)+
    lam*inner ℂ (WithLp.fstL 2 ℂ CubicThetaGlobalL2 CubicThetaGradientL2 u) (cubicThetaGlobalMass G)-
    inner ℂ (WithLp.fstL 2 ℂ CubicThetaGlobalL2 CubicThetaGradientL2 u)
      ((cubicThetaCompactSection_memLp J hJ).toLp _))
  fun_prop

lemma cubicThetaSmoothWeakDefect_C1 (G : cubicThetaSmoothTests) (J : CubicThetaSection)
    (hJ : HasCompactSupport (cubicThetaSectionNorm J)) (lam : ℂ)
    (F : CubicThetaSection)
    (hF : ContDiffOn ℝ 1 (cubicThetaSectionFunction F) {y : ℂ × ℝ | 0<y.2})
    (hc : HasCompactSupport (cubicThetaSectionNorm F)) :
    cubicThetaSmoothWeakDefect G J hJ lam (cubicThetaC1EnergyData F hF hc)=
      (∫ q, cubicThetaC1Pairing F G q ∂cubicThetaQuotientMeasure)+
      lam*(∫ q, cubicThetaSectionPairing F G q ∂cubicThetaQuotientMeasure)-
      ∫ q, cubicThetaSectionPairing F J q ∂cubicThetaQuotientMeasure := by
  change inner ℂ ((cubicThetaC1Gradient_memLp F hF hc).toLp _)
      ((cubicThetaGradientRepresentative_memLp G).toLp _)+
    lam*inner ℂ ((cubicThetaCompactSection_memLp F hc).toLp _)
      ((cubicThetaSectionRepresentative_memLp G).toLp _)-
    inner ℂ ((cubicThetaCompactSection_memLp F hc).toLp _)
      ((cubicThetaCompactSection_memLp J hJ).toLp _)=_
  rw [cubicThetaC1Pairing_L2 F G hF (G.property.1.of_le (by simp)),
    cubicThetaSectionPairing_L2,cubicThetaSectionPairing_L2]

lemma cubicThetaSmoothWeakDefect_coordinate (G : cubicThetaSmoothTests) (J : CubicThetaSection)
    (hJ : HasCompactSupport (cubicThetaSectionNorm J)) (lam : ℂ)
    (hEq : ∀ p : ℂ × ℝ, 0<p.2 →
      cubicThetaCoordinateLaplacian (cubicThetaSectionFunction G) p=
        lam*cubicThetaSectionFunction G p-cubicThetaSectionFunction J p)
    {g : ℂ × ℝ → ℂ} (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g)
    {K : Set (ℂ × ℝ)} (hK : IsCompact K) (hp : K⊆{y : ℂ × ℝ | 0<y.2})
    (hgs : tsupport g⊆K)
    (e : OpenPartialHomeomorph CubicThetaPoint CubicThetaQuotient)
    (he : (e : CubicThetaPoint → CubicThetaQuotient)=cubicThetaQuotientMap)
    (hKe : cubicThetaPointInclusion.symm '' K⊆e.source) :
    cubicThetaSmoothWeakDefect G J hJ lam (cubicThetaCoordinateData hg hc (hgs.trans hp))=0 := by
  rw [cubicThetaCoordinateData,cubicThetaSmoothWeakDefect_C1]
  exact sub_eq_zero.mpr (cubicThetaSmooth_chart_weak G J lam hEq hg hc hK hp hgs e he hKe)

end CubicFirstMoment

end

end OAI
