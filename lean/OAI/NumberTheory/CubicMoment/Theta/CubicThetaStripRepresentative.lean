import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCuspFourierIntegral

namespace OAI

/-! A measurable coordinate representative of every actual cusp L2
vector, with its first and second moment densities on the literal cell. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace CubicFirstMoment

def cubicThetaStripRepresentative (F : CubicThetaStripL2) : ℂ × ℝ → ℂ :=
  Function.extend cubicThetaPointCoordinates (F : CubicThetaPoint → ℂ) 0

lemma cubicThetaStripRepresentative_coordinates (F : CubicThetaStripL2) (p : CubicThetaPoint) :
    cubicThetaStripRepresentative F (cubicThetaPointCoordinates p)=F p :=
  cubicThetaPointInclusion_measurableEmbedding.injective.extend_apply _ _ _

lemma cubicThetaStripRepresentative_measurable (F : CubicThetaStripL2) :
    StronglyMeasurable (cubicThetaStripRepresentative F) :=
  cubicThetaPointInclusion_measurableEmbedding.stronglyMeasurable_extend
    (Lp.stronglyMeasurable F) stronglyMeasurable_zero

lemma cubicThetaStripRepresentative_integrable (F : CubicThetaStripL2) :
    IntegrableOn (fun y : ℂ × ℝ => cubicThetaStripRepresentative F y/(y.2:ℂ)^3)
      (cubicThetaHorizontalCell ×ˢ Ioi (2:ℝ)) := by
  have hi : IntegrableOn (fun p : CubicThetaPoint =>
      cubicThetaStripRepresentative F (cubicThetaPointCoordinates p))
      (cubicThetaCuspStrip 2) cubicThetaPointMeasure := by
    apply ((Lp.memLp F).integrable (by norm_num : (1:ℝ≥0∞)≤2)).congr
    filter_upwards with p
    rw [cubicThetaStripRepresentative_coordinates]
  have he := (cubicThetaPointIntegrable_complex_density (cubicThetaCuspStrip_measurable 2)
    (cubicThetaStripRepresentative F)).mp hi
  rwa [cubicThetaCuspStrip_coordinates (by norm_num : (0:ℝ)≤2)] at he

lemma cubicThetaStripRepresentative_sq_integrable (F : CubicThetaStripL2) :
    IntegrableOn (fun y : ℂ × ℝ => ‖cubicThetaStripRepresentative F y‖^2/y.2^3)
      (cubicThetaHorizontalCell ×ˢ Ioi (2:ℝ)) := by
  have hi : IntegrableOn (fun p : CubicThetaPoint =>
      ‖cubicThetaStripRepresentative F (cubicThetaPointCoordinates p)‖^2)
      (cubicThetaCuspStrip 2) cubicThetaPointMeasure := by
    apply ((memLp_two_iff_integrable_sq_norm
      (Lp.stronglyMeasurable F).aestronglyMeasurable).mp (Lp.memLp F)).congr
    filter_upwards with p
    rw [cubicThetaStripRepresentative_coordinates]
  have he := (cubicThetaPointIntegrable_density (cubicThetaCuspStrip_measurable 2)
    (fun y => ‖cubicThetaStripRepresentative F y‖^2)).mp hi
  rwa [cubicThetaCuspStrip_coordinates (by norm_num : (0:ℝ)≤2)] at he

lemma cubicThetaStripRepresentative_pair_integrable (F : CubicThetaStripL2)
    (h : Eisenstein) (W : CompactlySupportedContinuousMap ℝ ℂ) :
    IntegrableOn (fun p : CubicThetaPoint =>
      star (W p.val.2*(Real.fourierChar (tracePair p.val.1 (cubicThetaRowFrequency h)):ℂ))*F p)
      (cubicThetaCuspStrip 2) cubicThetaPointMeasure := by
  have hi := L2.integrable_inner (𝕜:=ℂ) (cubicThetaCuspFourierTest h W) F
  apply hi.congr
  filter_upwards [(cubicThetaCuspFourierWeight_memLp h W).coeFn_toLp] with p hp
  change inner ℂ (((cubicThetaCuspFourierWeight_memLp h W).toLp _) p) (F p)=_
  rw [hp,RCLike.inner_apply]
  simp only [starRingEnd_apply,cubicThetaCuspFourierWeight]
  ring

theorem cubicThetaStripRepresentative_pairing (F : CubicThetaStripL2)
    (h : Eisenstein) (W : CompactlySupportedContinuousMap ℝ ℂ) :
    inner ℂ (cubicThetaCuspFourierTest h W) F=
      ∫ v in Ioi (2:ℝ),star (W v)/(v:ℂ)^3*
        ∫ z in cubicThetaHorizontalCell,
          star (Real.fourierChar (tracePair z (cubicThetaRowFrequency h)):ℂ)*
            cubicThetaStripRepresentative F (z,v) := by
  have hi : IntegrableOn (fun p : CubicThetaPoint =>
      star (W p.val.2*(Real.fourierChar (tracePair p.val.1 (cubicThetaRowFrequency h)):ℂ))*
        cubicThetaStripRepresentative F (cubicThetaPointCoordinates p))
      (cubicThetaCuspStrip 2) cubicThetaPointMeasure := by
    simpa only [cubicThetaStripRepresentative_coordinates] using
      cubicThetaStripRepresentative_pair_integrable F h W
  have he := cubicThetaCuspStrip_fubini
    (fun y => star (W y.2*(Real.fourierChar (tracePair y.1 (cubicThetaRowFrequency h)):ℂ))*
      cubicThetaStripRepresentative F y) hi
  change (∫ p in cubicThetaCuspStrip 2,
    star (W p.val.2*(Real.fourierChar (tracePair p.val.1 (cubicThetaRowFrequency h)):ℂ))*
      cubicThetaStripRepresentative F (cubicThetaPointCoordinates p) ∂cubicThetaPointMeasure)=_ at he
  rw [L2.inner_def]
  calc
    _ = ∫ p in cubicThetaCuspStrip 2,
        star (W p.val.2*(Real.fourierChar (tracePair p.val.1 (cubicThetaRowFrequency h)):ℂ))*
          cubicThetaStripRepresentative F (cubicThetaPointCoordinates p) ∂cubicThetaPointMeasure := by
      apply integral_congr_ae
      filter_upwards [(cubicThetaCuspFourierWeight_memLp h W).coeFn_toLp] with p hp
      change inner ℂ (((cubicThetaCuspFourierWeight_memLp h W).toLp _) p) (F p)=_
      rw [hp,cubicThetaStripRepresentative_coordinates,RCLike.inner_apply]
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

end CubicFirstMoment

end

end OAI
