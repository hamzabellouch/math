import OAI.NumberTheory.CubicMoment.Theta.CubicThetaC1Energy

namespace OAI

/-! Compact C1 sections have genuine value-gradient L2 data, before
any assertion that they belong to the closed smooth energy graph. -/
noncomputable section
open Set Filter Topology MeasureTheory
namespace CubicFirstMoment

def cubicThetaC1QuotientEnergy (F : CubicThetaSection) (q : CubicThetaQuotient) : ℝ :=
  cubicThetaSectionEnergy F (cubicThetaQuotientLift q)

lemma cubicThetaC1QuotientEnergy_apply (F : CubicThetaSection)
    (hF : ContDiffOn ℝ 1 (cubicThetaSectionFunction F) {y : ℂ × ℝ | 0<y.2})
    (p : CubicThetaPoint) :
    cubicThetaC1QuotientEnergy F (cubicThetaQuotientMap p)=cubicThetaSectionEnergy F p := by
  have he := cubicThetaQuotientLift_map (cubicThetaQuotientMap p)
  obtain ⟨g,hg⟩ := cubicThetaQuotient_covering.apply_eq_iff_mem_orbit.mp he
  unfold cubicThetaC1QuotientEnergy
  rw [← hg,cubicThetaC1Energy_invariant F hF]

lemma cubicThetaC1QuotientEnergy_continuous (F : CubicThetaSection)
    (hF : ContDiffOn ℝ 1 (cubicThetaSectionFunction F) {y : ℂ × ℝ | 0<y.2}) :
    Continuous (cubicThetaC1QuotientEnergy F) := by
  apply cubicThetaQuotientMap_open.isQuotientMap.continuous_iff.mpr
  have he : cubicThetaC1QuotientEnergy F ∘ cubicThetaQuotientMap=cubicThetaSectionEnergy F :=
    funext (cubicThetaC1QuotientEnergy_apply F hF)
  rw [he]
  exact cubicThetaC1Energy_continuous F hF

lemma cubicThetaC1QuotientEnergy_compact (F : CubicThetaSection)
    (hc : HasCompactSupport (cubicThetaSectionNorm F)) :
    HasCompactSupport (cubicThetaC1QuotientEnergy F) := by
  apply hc.mono'
  intro q hq
  by_contra hn
  have hp : cubicThetaQuotientMap (cubicThetaQuotientLift q)∉tsupport (cubicThetaSectionNorm F) := by
    rwa [cubicThetaQuotientLift_map]
  have hd := cubicThetaSectionDifferential_eq_zero F (cubicThetaQuotientLift q) hp
  apply hq
  simp only [cubicThetaC1QuotientEnergy,cubicThetaSectionEnergy,hd,
    cubicThetaTangentEnergy,zero_apply,norm_zero,zero_pow (by norm_num : (2:ℕ)≠0),
    Finset.sum_const_zero,mul_zero]

lemma cubicThetaC1Gradient_continuous (F : CubicThetaSection)
    (hF : ContDiffOn ℝ 1 (cubicThetaSectionFunction F) {y : ℂ × ℝ | 0<y.2}) :
    Continuous (cubicThetaSectionGradient F) := by
  have hd : Continuous (fun p : CubicThetaPoint => fderiv ℝ (cubicThetaSectionFunction F) p.val) :=
    (hF.continuousOn_fderiv_of_isOpen
      (isOpen_lt continuous_const continuous_snd) (by norm_num)).comp_continuous
      continuous_subtype_val (fun p => p.property)
  apply (PiLp.continuous_toLp _ _).comp
  apply continuous_pi
  intro i
  exact (continuous_snd.comp continuous_subtype_val).smul (hd.clm_apply continuous_const)

lemma cubicThetaC1Gradient_norm_sq (F : CubicThetaSection)
    (hF : ContDiffOn ℝ 1 (cubicThetaSectionFunction F) {y : ℂ × ℝ | 0<y.2}) (q : CubicThetaQuotient) :
    ‖cubicThetaGradientRepresentative F q‖^2=cubicThetaC1QuotientEnergy F q := by
  unfold cubicThetaGradientRepresentative
  rw [cubicThetaSectionGradient_norm_sq,← cubicThetaC1QuotientEnergy_apply F hF,
    cubicThetaBorelSection_rightInverse]

lemma cubicThetaC1Gradient_memLp (F : CubicThetaSection)
    (hF : ContDiffOn ℝ 1 (cubicThetaSectionFunction F) {y : ℂ × ℝ | 0<y.2})
    (hc : HasCompactSupport (cubicThetaSectionNorm F)) :
    MemLp (cubicThetaGradientRepresentative F) 2 cubicThetaQuotientMeasure := by
  have hm : Measurable (cubicThetaGradientRepresentative F) :=
    (cubicThetaC1Gradient_continuous F hF).measurable.comp cubicThetaBorelSection_measurable
  apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr
  simpa only [cubicThetaC1Gradient_norm_sq F hF] using
    (cubicThetaC1QuotientEnergy_continuous F hF).integrable_of_hasCompactSupport
      (cubicThetaC1QuotientEnergy_compact F hc)

lemma cubicThetaCompactSection_memLp (F : CubicThetaSection)
    (hc : HasCompactSupport (cubicThetaSectionNorm F)) :
    MemLp (cubicThetaSectionRepresentative F) 2 cubicThetaQuotientMeasure := by
  apply (memLp_norm_iff (cubicThetaSectionRepresentative_measurable F).aestronglyMeasurable).mp
  simpa only [cubicThetaSectionRepresentative_norm] using
    (cubicThetaSectionNorm_continuous F).memLp_of_hasCompactSupport hc

def cubicThetaC1EnergyData (F : CubicThetaSection)
    (hF : ContDiffOn ℝ 1 (cubicThetaSectionFunction F) {y : ℂ × ℝ | 0<y.2})
    (hc : HasCompactSupport (cubicThetaSectionNorm F)) : CubicThetaGlobalEnergyAmbient :=
  WithLp.toLp 2 ((cubicThetaCompactSection_memLp F hc).toLp _,
    (cubicThetaC1Gradient_memLp F hF hc).toLp _)

end CubicFirstMoment

end

end OAI
