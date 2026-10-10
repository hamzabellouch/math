import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCoordinateChartIntegral
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCoordinatePairing
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCoordinateSectionSupport
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaSectionPairing

namespace OAI

/-! Pairing a section with one compact periodized chart function is
exactly its coordinate mass and gradient pairing. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaC1Pairing_support (F G : CubicThetaSection) :
    tsupport (cubicThetaC1Pairing F G)⊆tsupport (cubicThetaSectionNorm F) := by
  apply closure_minimal _ (isClosed_tsupport _)
  intro q hq
  by_contra hout
  have hp : cubicThetaQuotientMap (cubicThetaQuotientLift q)∉tsupport (cubicThetaSectionNorm F) := by
    rwa [cubicThetaQuotientLift_map]
  have hd := cubicThetaSectionDifferential_eq_zero F (cubicThetaQuotientLift q) hp
  have hg : cubicThetaSectionGradient F (cubicThetaQuotientLift q)=0 := by
    ext i
    simp [cubicThetaSectionGradient,hd]
  exact hq (by simp only [cubicThetaC1Pairing,hg,inner_zero_left])

lemma cubicThetaCoordinatePairing_fderiv_congr {f g h : ℂ × ℝ → ℂ} {p : ℂ × ℝ}
    (hf : DifferentiableAt ℝ f p) (hg : DifferentiableAt ℝ g p)
    (he : fderiv ℝ f p=fderiv ℝ g p) :
    cubicThetaCoordinatePairing f h p=cubicThetaCoordinatePairing g h p := by
  unfold cubicThetaCoordinatePairing
  simp only [cubicThetaAxisFirst_eq_fderiv _ _ hf,cubicThetaAxisFirst_eq_fderiv _ _ hg,he]

lemma cubicThetaCoordinateSection_mass_pairing {g : ℂ × ℝ → ℂ}
    (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g)
    {K : Set (ℂ × ℝ)} (hK : IsCompact K) (hp : K⊆{y : ℂ × ℝ | 0<y.2})
    (hgs : tsupport g⊆K)
    (e : OpenPartialHomeomorph CubicThetaPoint CubicThetaQuotient)
    (he : (e : CubicThetaPoint → CubicThetaQuotient)=cubicThetaQuotientMap)
    (hKe : cubicThetaPointInclusion.symm '' K⊆e.source) (G : CubicThetaSection) :
    let P := cubicThetaPoincareSection (cubicThetaCoordinateSeed g hg.continuous hc (hgs.trans hp))
    (∫ q, cubicThetaSectionPairing P G q ∂cubicThetaQuotientMeasure)=
      ∫ y in K, star (g y)*cubicThetaSectionFunction G y/(y.2:ℂ)^3 := by
  intro P
  have hs : tsupport (cubicThetaCoordinateSeed g hg.continuous hc (hgs.trans hp))⊆
      cubicThetaPointInclusion.symm '' K :=
    (cubicThetaCoordinateSeed_support _ _ _ _).trans (image_mono hgs)
  apply cubicThetaCoordinateChart_integral e he hK hp hKe _
    (cubicThetaSectionPairing_continuous P G).stronglyMeasurable
  · exact (subset_tsupport _).trans ((cubicThetaSectionPairing_support P G).trans
      ((cubicThetaPoincareSection_norm_support _).trans (image_mono hs)))
  · intro p hps
    rw [cubicThetaSectionPairing_apply]
    have hv := cubicThetaPoincareSection_on_sheet
      (cubicThetaCoordinateSeed g hg.continuous hc (hgs.trans hp)) e he
      ((subset_tsupport _).trans (hs.trans hKe)) (hKe hps)
    change P.val p=g p.val at hv
    rw [hv]
    rw [cubicThetaSectionFunction_apply G p.property]
    simp only [RCLike.inner_apply,starRingEnd_apply]
    change G.val p*star (g p.val)=star (g p.val)*G.val p
    ring

lemma cubicThetaCoordinateSection_gradient_pairing {g : ℂ × ℝ → ℂ}
    (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g)
    {K : Set (ℂ × ℝ)} (hK : IsCompact K) (hp : K⊆{y : ℂ × ℝ | 0<y.2})
    (hgs : tsupport g⊆K)
    (e : OpenPartialHomeomorph CubicThetaPoint CubicThetaQuotient)
    (he : (e : CubicThetaPoint → CubicThetaQuotient)=cubicThetaQuotientMap)
    (hKe : cubicThetaPointInclusion.symm '' K⊆e.source) (G : CubicThetaSection)
    (hG : ContDiffOn ℝ 1 (cubicThetaSectionFunction G) {y : ℂ × ℝ | 0<y.2}) :
    let P := cubicThetaPoincareSection (cubicThetaCoordinateSeed g hg.continuous hc (hgs.trans hp))
    (∫ q, cubicThetaC1Pairing P G q ∂cubicThetaQuotientMeasure)=
      ∫ y in K, cubicThetaHeightInverse y*cubicThetaCoordinatePairing g (cubicThetaSectionFunction G) y := by
  intro P
  have hP := cubicThetaCoordinateSection_regular hg hc (hgs.trans hp)
  have hs : tsupport (cubicThetaCoordinateSeed g hg.continuous hc (hgs.trans hp))⊆
      cubicThetaPointInclusion.symm '' K :=
    (cubicThetaCoordinateSeed_support _ _ _ _).trans (image_mono hgs)
  have ht := (subset_tsupport _).trans (hs.trans hKe)
  have hchart : (∫ q, cubicThetaC1Pairing P G q ∂cubicThetaQuotientMeasure)=
      ∫ y in K, ((y.2:ℂ)^2*cubicThetaCoordinatePairing g (cubicThetaSectionFunction G) y)/(y.2:ℂ)^3 := by
    apply cubicThetaCoordinateChart_integral e he hK hp hKe _
      (cubicThetaC1Pairing_continuous P G hP hG).stronglyMeasurable
    · exact (subset_tsupport _).trans ((cubicThetaC1Pairing_support P G).trans
        ((cubicThetaPoincareSection_norm_support _).trans (image_mono hs)))
    · intro p hps
      rw [cubicThetaC1Pairing_apply P G hP hG,cubicThetaSectionGradient_pair_coordinates P G hP hG]
      have hleft : cubicThetaPointInclusion.symm p.val=p :=
        cubicThetaPointInclusion.left_inv (by rw [cubicThetaPointInclusion_source]; trivial)
      have hd := cubicThetaCoordinateSection_fderiv_on_sheet g hg.continuous hc (hgs.trans hp)
        e he ht p.property (by rw [hleft]; exact hKe hps)
      rw [cubicThetaCoordinatePairing_fderiv_congr
        ((hP.contDiffAt ((isOpen_lt continuous_const continuous_snd).mem_nhds p.property)).differentiableAt (by norm_num))
        (hg.differentiable one_ne_zero p.val) hd]
  rw [hchart]
  apply setIntegral_congr_fun hK.measurableSet
  intro y hy
  have hv : (y.2:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (hp hy).ne'
  simp only [cubicThetaHeightInverse,Complex.ofReal_inv]
  field_simp [hv]

end CubicFirstMoment

end

end OAI
