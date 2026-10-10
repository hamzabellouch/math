import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCoordinateSectionPairing
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaArithmeticLocalWeak
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaArithmeticEnergy
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaForcingCore

namespace OAI

/-! The coordinate weak equation descends, with its exact measure, to
compactly supported periodized tests in every injective sheet. -/
noncomputable section
open Set Filter Topology MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaCoordinatePairing_zero_left {g f : ℂ × ℝ → ℂ} {p : ℂ × ℝ}
    (hp : p∉tsupport g) : cubicThetaCoordinatePairing g f p=0 := by
  have hz (k : CubicThetaAxis) : cubicThetaAxisFirst k g p=0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hp (cubicThetaAxisFirst_support k g h))
  simp only [cubicThetaCoordinatePairing,hz,star_zero,zero_mul,add_zero]

lemma cubicThetaArithmeticSectionFunction_axisFirst {s : ℂ} (hs : 2<s.re)
    (k : CubicThetaAxis) {p : ℂ × ℝ} (hp : 0<p.2) :
    cubicThetaAxisFirst k (cubicThetaSectionFunction (cubicThetaArithmeticSection s hs)) p=
      cubicThetaAxisFirst k (fun y => cubicThetaArithmeticRemainder y s) p := by
  have he : cubicThetaSectionFunction (cubicThetaArithmeticSection s hs)=ᶠ[𝓝 p]
      (fun y => cubicThetaArithmeticRemainder y s) := by
    filter_upwards [(isOpen_lt continuous_const continuous_snd).mem_nhds hp] with y hy
    rw [cubicThetaSectionFunction_apply _ hy]
    rfl
  have hf := ((cubicThetaArithmeticSectionFunction_contDiffOn_one hs).contDiffAt
    ((isOpen_lt continuous_const continuous_snd).mem_nhds hp)).differentiableAt (by norm_num)
  have hg := ((cubicThetaArithmeticRemainder_contDiffOn_one hs).contDiffAt
    ((isOpen_lt continuous_const continuous_snd).mem_nhds hp)).differentiableAt (by norm_num)
  rw [cubicThetaAxisFirst_eq_fderiv _ _ hf,cubicThetaAxisFirst_eq_fderiv _ _ hg,he.fderiv_eq]

lemma cubicThetaArithmetic_chart_weak {s : ℂ} (hs : 2<s.re)
    {g : ℂ × ℝ → ℂ} (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g)
    {K : Set (ℂ × ℝ)} (hK : IsCompact K) (hp : K⊆{y : ℂ × ℝ | 0<y.2})
    (hgs : tsupport g⊆K)
    (e : OpenPartialHomeomorph CubicThetaPoint CubicThetaQuotient)
    (he : (e : CubicThetaPoint → CubicThetaQuotient)=cubicThetaQuotientMap)
    (hKe : cubicThetaPointInclusion.symm '' K⊆e.source) :
    let P := cubicThetaPoincareSection (cubicThetaCoordinateSeed g hg.continuous hc (hgs.trans hp))
    (∫ q, cubicThetaC1Pairing P (cubicThetaArithmeticSection s hs) q ∂cubicThetaQuotientMeasure)+
      s*(s-2)*(∫ q, cubicThetaSectionPairing P (cubicThetaArithmeticSection s hs) q
        ∂cubicThetaQuotientMeasure)=
      ∫ q, cubicThetaSectionPairing P (cubicThetaForcingSection s) q ∂cubicThetaQuotientMeasure := by
  intro P
  rw [cubicThetaCoordinateSection_gradient_pairing hg hc hK hp hgs e he hKe _
    (cubicThetaArithmeticSectionFunction_contDiffOn_one hs),
    cubicThetaCoordinateSection_mass_pairing hg hc hK hp hgs e he hKe,
    cubicThetaCoordinateSection_mass_pairing hg hc hK hp hgs e he hKe]
  have hG : (∫ y in K, cubicThetaHeightInverse y*cubicThetaCoordinatePairing g
      (cubicThetaSectionFunction (cubicThetaArithmeticSection s hs)) y)=
      ∫ y, cubicThetaHeightInverse y*cubicThetaCoordinatePairing g
        (fun z => cubicThetaArithmeticRemainder z s) y := by
    calc
      _ = ∫ y in K, cubicThetaHeightInverse y*cubicThetaCoordinatePairing g
          (fun z => cubicThetaArithmeticRemainder z s) y := by
        apply setIntegral_congr_fun hK.measurableSet
        intro y hy
        simp only [cubicThetaCoordinatePairing,cubicThetaArithmeticSectionFunction_axisFirst hs _ (hp hy)]
      _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => by
        rw [cubicThetaCoordinatePairing_zero_left (fun h => hy (hgs h)),mul_zero])
  have hM : (∫ y in K, star (g y)*cubicThetaSectionFunction (cubicThetaArithmeticSection s hs) y/(y.2:ℂ)^3)=
      ∫ y, star (g y)*cubicThetaArithmeticRemainder y s/(y.2:ℂ)^3 := by
    calc
      _ = ∫ y in K, star (g y)*cubicThetaArithmeticRemainder y s/(y.2:ℂ)^3 := by
        apply setIntegral_congr_fun hK.measurableSet
        intro y hy
        dsimp only
        rw [cubicThetaSectionFunction_apply _ (hp hy)]
        rfl
      _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => by
        rw [image_eq_zero_of_notMem_tsupport (fun h => hy (hgs h)),star_zero,zero_mul,zero_div])
  have hF : (∫ y in K, star (g y)*cubicThetaSectionFunction (cubicThetaForcingSection s) y/(y.2:ℂ)^3)=
      ∫ y, star (g y)*cubicThetaForcingSeries y s/(y.2:ℂ)^3 := by
    calc
      _ = ∫ y in K, star (g y)*cubicThetaForcingSeries y s/(y.2:ℂ)^3 := by
        apply setIntegral_congr_fun hK.measurableSet
        intro y hy
        dsimp only
        rw [cubicThetaSectionFunction_apply _ (hp hy)]
        rfl
      _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => by
        rw [image_eq_zero_of_notMem_tsupport (fun h => hy (hgs h)),star_zero,zero_mul,zero_div])
  rw [hG,hM,hF]
  exact cubicThetaArithmetic_local_weak hs g hg hc (hgs.trans hp)

end CubicFirstMoment

end

end OAI
