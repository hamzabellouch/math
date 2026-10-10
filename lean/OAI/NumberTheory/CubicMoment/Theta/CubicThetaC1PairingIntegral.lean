import OAI.NumberTheory.CubicMoment.Theta.CubicThetaC1Pairing

namespace OAI

/-! Quotient integration of the actual differential pairing agrees
with the Hilbert L2 inner product. Compact tests give compact support. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaC1Pairing_compact (F G : CubicThetaSection)
    (hc : HasCompactSupport (cubicThetaSectionNorm F)) :
    HasCompactSupport (cubicThetaC1Pairing F G) := by
  apply hc.mono'
  intro q hq
  by_contra hout
  have hp : cubicThetaQuotientMap (cubicThetaQuotientLift q)∉tsupport (cubicThetaSectionNorm F) := by
    rwa [cubicThetaQuotientLift_map]
  have hd := cubicThetaSectionDifferential_eq_zero F (cubicThetaQuotientLift q) hp
  have hz : cubicThetaSectionGradient F (cubicThetaQuotientLift q)=0 := by
    ext i
    simp [cubicThetaSectionGradient,hd]
  exact hq (by simp only [cubicThetaC1Pairing,hz,inner_zero_left])

lemma cubicThetaC1Pairing_integrable (F G : CubicThetaSection)
    (hF : ContDiffOn ℝ 1 (cubicThetaSectionFunction F) {y : ℂ × ℝ | 0<y.2})
    (hG : ContDiffOn ℝ 1 (cubicThetaSectionFunction G) {y : ℂ × ℝ | 0<y.2})
    (hc : HasCompactSupport (cubicThetaSectionNorm F)) :
    Integrable (cubicThetaC1Pairing F G) cubicThetaQuotientMeasure :=
  (cubicThetaC1Pairing_continuous F G hF hG).integrable_of_hasCompactSupport
    (cubicThetaC1Pairing_compact F G hc)

lemma cubicThetaC1Pairing_L2 (F G : CubicThetaSection)
    (hF : ContDiffOn ℝ 1 (cubicThetaSectionFunction F) {y : ℂ × ℝ | 0<y.2})
    (hG : ContDiffOn ℝ 1 (cubicThetaSectionFunction G) {y : ℂ × ℝ | 0<y.2})
    (hmF : MemLp (cubicThetaGradientRepresentative F) 2 cubicThetaQuotientMeasure)
    (hmG : MemLp (cubicThetaGradientRepresentative G) 2 cubicThetaQuotientMeasure) :
    inner ℂ (hmF.toLp _) (hmG.toLp _)=∫ q, cubicThetaC1Pairing F G q ∂cubicThetaQuotientMeasure := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hmF.coeFn_toLp,hmG.coeFn_toLp] with q hqF hqG
  rw [hqF,hqG,cubicThetaC1Pairing_representative F G hF hG]

end CubicFirstMoment

end

end OAI
