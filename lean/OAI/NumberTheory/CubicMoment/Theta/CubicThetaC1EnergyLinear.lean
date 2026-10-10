import OAI.NumberTheory.CubicMoment.Theta.CubicThetaC1EnergyNorm

namespace OAI

/-! Subtraction of actual compact C1 value-gradient data agrees with
subtraction in the Hilbert ambient space. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaC1EnergyData_congr {F G : CubicThetaSection} (he : F=G)
    (hF : ContDiffOn ℝ 1 (cubicThetaSectionFunction F) {y : ℂ × ℝ | 0<y.2})
    (hG : ContDiffOn ℝ 1 (cubicThetaSectionFunction G) {y : ℂ × ℝ | 0<y.2})
    (hcF : HasCompactSupport (cubicThetaSectionNorm F))
    (hcG : HasCompactSupport (cubicThetaSectionNorm G)) :
    cubicThetaC1EnergyData F hF hcF=cubicThetaC1EnergyData G hG hcG := by
  subst G
  rfl

lemma cubicThetaCompactSection_sub (F G : CubicThetaSection)
    (hF : HasCompactSupport (cubicThetaSectionNorm F))
    (hG : HasCompactSupport (cubicThetaSectionNorm G)) :
    HasCompactSupport (cubicThetaSectionNorm (F-G)) := by
  apply (hF.union hG).of_isClosed_subset isClosed_closure
  apply closure_minimal _ (hF.union hG).isClosed
  intro q hq
  by_contra h
  have hFq : cubicThetaSectionNorm F q=0 :=
    image_eq_zero_of_notMem_tsupport (fun hFq => h (Or.inl hFq))
  have hGq : cubicThetaSectionNorm G q=0 :=
    image_eq_zero_of_notMem_tsupport (fun hGq => h (Or.inr hGq))
  apply hq
  change ‖F.val (cubicThetaQuotientLift q)-G.val (cubicThetaQuotientLift q)‖=0
  rw [norm_eq_zero.mp hFq,norm_eq_zero.mp hGq,sub_self,norm_zero]

lemma cubicThetaC1Gradient_sub (F G : CubicThetaSection)
    (hF : ContDiffOn ℝ 1 (cubicThetaSectionFunction F) {y : ℂ × ℝ | 0<y.2})
    (hG : ContDiffOn ℝ 1 (cubicThetaSectionFunction G) {y : ℂ × ℝ | 0<y.2}) (p : CubicThetaPoint) :
    cubicThetaSectionGradient (F-G) p=cubicThetaSectionGradient F p-cubicThetaSectionGradient G p := by
  have hdF := (hF.contDiffAt ((isOpen_lt continuous_const continuous_snd).mem_nhds p.property)).differentiableAt (by norm_num)
  have hdG := (hG.contDiffAt ((isOpen_lt continuous_const continuous_snd).mem_nhds p.property)).differentiableAt (by norm_num)
  have he : cubicThetaSectionFunction (F-G)=cubicThetaSectionFunction F-cubicThetaSectionFunction G := rfl
  ext i
  simp only [cubicThetaSectionGradient,cubicThetaSectionDifferential,he,fderiv_sub hdF hdG,
    ContinuousLinearMap.comp_apply,sub_apply,smul_sub]
  rfl

lemma cubicThetaC1EnergyData_sub (F G : CubicThetaSection)
    (hF : ContDiffOn ℝ 1 (cubicThetaSectionFunction F) {y : ℂ × ℝ | 0<y.2})
    (hG : ContDiffOn ℝ 1 (cubicThetaSectionFunction G) {y : ℂ × ℝ | 0<y.2})
    (hcF : HasCompactSupport (cubicThetaSectionNorm F))
    (hcG : HasCompactSupport (cubicThetaSectionNorm G)) :
    cubicThetaC1EnergyData (F-G) (hF.sub hG) (cubicThetaCompactSection_sub F G hcF hcG)=
      cubicThetaC1EnergyData F hF hcF-cubicThetaC1EnergyData G hG hcG := by
  have hcD := cubicThetaCompactSection_sub F G hcF hcG
  have hD : ContDiffOn ℝ 1 (cubicThetaSectionFunction (F-G)) {y : ℂ × ℝ | 0<y.2} := hF.sub hG
  apply (WithLp.prodContinuousLinearEquiv 2 ℂ CubicThetaGlobalL2 CubicThetaGradientL2).injective
  apply Prod.ext
  · change (cubicThetaCompactSection_memLp (F-G) hcD).toLp _=
      (cubicThetaCompactSection_memLp F hcF).toLp _-(cubicThetaCompactSection_memLp G hcG).toLp _
    apply Lp.ext
    filter_upwards [(cubicThetaCompactSection_memLp (F-G) hcD).coeFn_toLp,
      (cubicThetaCompactSection_memLp F hcF).coeFn_toLp,
      (cubicThetaCompactSection_memLp G hcG).coeFn_toLp,
      Lp.coeFn_sub ((cubicThetaCompactSection_memLp F hcF).toLp _)
        ((cubicThetaCompactSection_memLp G hcG).toLp _)] with q hD hFq hGq hs
    simp only [Pi.sub_apply] at hs
    rw [hD,hs,hFq,hGq]
    rfl
  · change (cubicThetaC1Gradient_memLp (F-G) hD hcD).toLp _=
      (cubicThetaC1Gradient_memLp F hF hcF).toLp _-(cubicThetaC1Gradient_memLp G hG hcG).toLp _
    apply Lp.ext
    filter_upwards [(cubicThetaC1Gradient_memLp (F-G) hD hcD).coeFn_toLp,
      (cubicThetaC1Gradient_memLp F hF hcF).coeFn_toLp,
      (cubicThetaC1Gradient_memLp G hG hcG).coeFn_toLp,
      Lp.coeFn_sub ((cubicThetaC1Gradient_memLp F hF hcF).toLp _)
        ((cubicThetaC1Gradient_memLp G hG hcG).toLp _)] with q hD hFq hGq hs
    simp only [Pi.sub_apply] at hs
    rw [hD,hs,hFq,hGq]
    exact cubicThetaC1Gradient_sub F G hF hG _

end CubicFirstMoment

end

end OAI
