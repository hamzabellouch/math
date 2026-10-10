import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPositiveStripRepresentative
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPositiveFourierMass
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPositiveModelObservation

namespace OAI

/-! Weighted Fourier pairing on the actual positive strip, and its
compatibility with the global energy restriction. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported ContDiff
namespace CubicFirstMoment

lemma cubicThetaPositiveStrip_inner_formula {ε : ℝ} (hε : 0<ε)
    (h : Eisenstein) (W : C_c(ℝ,ℂ)) (f : ℂ × ℝ → ℂ)
    (hf : MemLp (fun p : CubicThetaPoint => f p.val) 2
      (cubicThetaPointMeasure.restrict (cubicThetaCuspStrip ε))) :
    inner ℂ (cubicThetaPositiveStripFourierTest hε h W) (hf.toLp _)=
      ∫ v in Ioi ε,star (W v)/(v:ℂ)^3*
        ∫ z in cubicThetaHorizontalCell,
          star (Real.fourierChar (tracePair z (cubicThetaRowFrequency h)):ℂ)*f (z,v) := by
  have hi := L2.integrable_inner (𝕜:=ℂ)
    (cubicThetaPositiveStripFourierTest hε h W) (hf.toLp _)
  have hp : IntegrableOn (fun p : CubicThetaPoint =>
      star (W p.val.2*(Real.fourierChar (tracePair p.val.1 (cubicThetaRowFrequency h)):ℂ))*f p.val)
      (cubicThetaCuspStrip ε) cubicThetaPointMeasure := by
    apply hi.congr
    filter_upwards [(cubicThetaPositiveFourierWeight_memLp hε h W).coeFn_toLp,
      hf.coeFn_toLp] with p hW hf
    change inner ℂ (((cubicThetaPositiveFourierWeight_memLp hε h W).toLp _) p) _=_
    rw [hW,hf,RCLike.inner_apply]
    simp only [starRingEnd_apply,cubicThetaCuspFourierWeight]
    ring
  have he := cubicThetaPositiveCuspStrip_fubini hε.le
    (fun y => star (W y.2*(Real.fourierChar (tracePair y.1 (cubicThetaRowFrequency h)):ℂ))*f y) hp
  change (∫ p in cubicThetaCuspStrip ε,
    star (W p.val.2*(Real.fourierChar (tracePair p.val.1 (cubicThetaRowFrequency h)):ℂ))*f p.val
      ∂cubicThetaPointMeasure)=_ at he
  rw [L2.inner_def]
  calc
    _ = ∫ p in cubicThetaCuspStrip ε,
        star (W p.val.2*(Real.fourierChar (tracePair p.val.1 (cubicThetaRowFrequency h)):ℂ))*f p.val
          ∂cubicThetaPointMeasure := by
      apply integral_congr_ae
      filter_upwards [(cubicThetaPositiveFourierWeight_memLp hε h W).coeFn_toLp,
        hf.coeFn_toLp] with p hW hf
      change inner ℂ (((cubicThetaPositiveFourierWeight_memLp hε h W).toLp _) p) _=_
      rw [hW,hf,RCLike.inner_apply]
      simp only [starRingEnd_apply,cubicThetaCuspFourierWeight]
      ring
    _ = _ := by
      rw [he]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro v _
      dsimp only
      rw [←integral_const_mul]
      apply setIntegral_congr_fun cubicThetaHorizontalCell_measurable
      intro z _
      simp only [star_mul]
      ring

lemma cubicThetaPositiveRestriction_finite_pairing {ε : ℝ} (hε : 0<ε)
    (h : Eisenstein) (W : C_c(ℝ,ℂ)) (hW : ∀ v≤ε,W v=0)
    (hsm : ContDiff ℝ ∞ (W : ℝ → ℂ)) (F : cubicThetaFiniteEnergySections) :
    inner ℂ (cubicThetaPositiveFourierProfileL2 h W hε hW) (cubicThetaFiniteEnergyValue F)=
      inner ℂ (cubicThetaPositiveStripFourierTest hε h W)
        (cubicThetaFinitePositiveCuspRestriction hε F) := by
  have hf : MemLp (fun p : CubicThetaPoint => cubicThetaSectionFunction F p.val) 2
      (cubicThetaPointMeasure.restrict (cubicThetaCuspStrip ε)) := by
    simpa only [cubicThetaSectionFunction_coordinates] using
      cubicThetaFiniteEnergy_positiveStrip_memLp hε F
  have he := cubicThetaPositiveFourierMass_pairing_finite h W hε hW hsm F
  change inner ℂ (cubicThetaPositiveFourierProfileL2 h W hε hW)
    (cubicThetaFiniteEnergyValue F)=_ at he
  rw [he,←cubicThetaPositiveRadialIntegral_zero_extension W hε.le hW]
  have hto : hf.toLp _=cubicThetaFinitePositiveCuspRestriction hε F := by
    apply Lp.ext
    filter_upwards [hf.coeFn_toLp,
      (cubicThetaFiniteEnergy_positiveStrip_memLp hε F).coeFn_toLp] with p hp hF
    change (hf.toLp _) p=((cubicThetaFiniteEnergy_positiveStrip_memLp hε F).toLp _) p
    rw [hp,hF,cubicThetaSectionFunction_coordinates]
  rw [←hto,cubicThetaPositiveStrip_inner_formula hε]
  rfl

theorem cubicThetaPositiveRestriction_pairing {ε : ℝ} (hε : 0<ε)
    (h : Eisenstein) (W : C_c(ℝ,ℂ)) (hW : ∀ v≤ε,W v=0)
    (hsm : ContDiff ℝ ∞ (W : ℝ → ℂ)) (u : cubicThetaGlobalEnergySpace) :
    inner ℂ (cubicThetaPositiveFourierProfileL2 h W hε hW) (cubicThetaGlobalInclusion u)=
      inner ℂ (cubicThetaPositiveStripFourierTest hε h W) (cubicThetaPositiveCuspRestriction hε u) := by
  refine cubicThetaFiniteEnergyEmbedding_dense.induction_on u
    (isClosed_eq (continuous_const.inner cubicThetaGlobalInclusion.continuous)
      (continuous_const.inner (cubicThetaPositiveCuspRestriction hε).continuous)) ?_
  intro F
  rw [cubicThetaFiniteEnergyEmbedding_value,cubicThetaPositiveCuspRestriction_finiteEnergy]
  exact cubicThetaPositiveRestriction_finite_pairing hε h W hW hsm F

theorem cubicThetaPositiveModelStrip_observations {ε : ℝ} (hε : 0<ε)
    (h : Eisenstein) (W : C_c(ℝ,ℂ)) (hW : ∀ v≤ε,W v=0)
    (hsm : ContDiff ℝ ∞ (W : ℝ → ℂ)) :
    inner ℂ (cubicThetaPositiveStripFourierTest hε h W)
      (cubicThetaPositiveCuspRestriction hε cubicThetaNormalizedArithmeticResidue)=
    inner ℂ (cubicThetaPositiveStripFourierTest hε h W)
      (cubicThetaPositiveModelStrip cubicThetaArithmeticBaseScalar hε) := by
  rw [←cubicThetaPositiveRestriction_pairing hε h W hW hsm,
    cubicThetaPositiveModel_all_observations h W hε hW,
    cubicThetaPositiveModelStrip,cubicThetaPositiveStrip_inner_formula hε]
  exact (cubicThetaPositiveRadialIntegral_zero_extension W hε.le hW _).symm

end CubicFirstMoment

end

end OAI
