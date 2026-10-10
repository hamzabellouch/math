import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPositiveModelL2
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPositiveStripFubini

namespace OAI

/-! A measurable coordinate representative of every positive-strip L2
vector, with its first and second moment densities on the literal cell. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace CubicFirstMoment
variable {ε : ℝ}

def cubicThetaPositiveStripRepresentative (F : CubicThetaPositiveStripL2 ε) : ℂ × ℝ → ℂ :=
  Function.extend cubicThetaPointCoordinates (F : CubicThetaPoint → ℂ) 0

lemma cubicThetaPositiveStripRepresentative_coordinates (F : CubicThetaPositiveStripL2 ε) (p : CubicThetaPoint) :
    cubicThetaPositiveStripRepresentative F (cubicThetaPointCoordinates p)=F p :=
  cubicThetaPointInclusion_measurableEmbedding.injective.extend_apply _ _ _

lemma cubicThetaPositiveStripRepresentative_measurable (F : CubicThetaPositiveStripL2 ε) :
    StronglyMeasurable (cubicThetaPositiveStripRepresentative F) :=
  cubicThetaPointInclusion_measurableEmbedding.stronglyMeasurable_extend
    (Lp.stronglyMeasurable F) stronglyMeasurable_zero

lemma cubicThetaPositiveStripRepresentative_integrable (hε : 0<ε) (F : CubicThetaPositiveStripL2 ε) :
    IntegrableOn (fun y : ℂ × ℝ => cubicThetaPositiveStripRepresentative F y/(y.2:ℂ)^3)
      (cubicThetaHorizontalCell ×ˢ Ioi ε) := by
  have := cubicThetaPositiveStrip_finite hε
  have hi : IntegrableOn (fun p : CubicThetaPoint =>
      cubicThetaPositiveStripRepresentative F (cubicThetaPointCoordinates p))
      (cubicThetaCuspStrip ε) cubicThetaPointMeasure := by
    apply ((Lp.memLp F).integrable (by norm_num : (1:ℝ≥0∞)≤2)).congr
    filter_upwards with p
    rw [cubicThetaPositiveStripRepresentative_coordinates]
  have he := (cubicThetaPointIntegrable_complex_density (cubicThetaCuspStrip_measurable ε)
    (cubicThetaPositiveStripRepresentative F)).mp hi
  rwa [cubicThetaCuspStrip_coordinates hε.le] at he

lemma cubicThetaPositiveStripRepresentative_sq_integrable (hε : 0<ε) (F : CubicThetaPositiveStripL2 ε) :
    IntegrableOn (fun y : ℂ × ℝ => ‖cubicThetaPositiveStripRepresentative F y‖^2/y.2^3)
      (cubicThetaHorizontalCell ×ˢ Ioi ε) := by
  have hi : IntegrableOn (fun p : CubicThetaPoint =>
      ‖cubicThetaPositiveStripRepresentative F (cubicThetaPointCoordinates p)‖^2)
      (cubicThetaCuspStrip ε) cubicThetaPointMeasure := by
    apply ((memLp_two_iff_integrable_sq_norm
      (Lp.stronglyMeasurable F).aestronglyMeasurable).mp (Lp.memLp F)).congr
    filter_upwards with p
    rw [cubicThetaPositiveStripRepresentative_coordinates]
  have he := (cubicThetaPointIntegrable_density (cubicThetaCuspStrip_measurable ε)
    (fun y => ‖cubicThetaPositiveStripRepresentative F y‖^2)).mp hi
  rwa [cubicThetaCuspStrip_coordinates hε.le] at he

lemma cubicThetaPositiveStripRepresentative_pair_integrable (hε : 0<ε) (F : CubicThetaPositiveStripL2 ε)
    (h : Eisenstein) (W : CompactlySupportedContinuousMap ℝ ℂ) :
    IntegrableOn (fun p : CubicThetaPoint =>
      star (W p.val.2*(Real.fourierChar (tracePair p.val.1 (cubicThetaRowFrequency h)):ℂ))*F p)
      (cubicThetaCuspStrip ε) cubicThetaPointMeasure := by
  have hi := L2.integrable_inner (𝕜:=ℂ) (cubicThetaPositiveStripFourierTest hε h W) F
  apply hi.congr
  filter_upwards [(cubicThetaPositiveFourierWeight_memLp hε h W).coeFn_toLp] with p hp
  change inner ℂ (((cubicThetaPositiveFourierWeight_memLp hε h W).toLp _) p) (F p)=_
  rw [hp,RCLike.inner_apply]
  simp only [starRingEnd_apply,cubicThetaCuspFourierWeight]
  ring

theorem cubicThetaPositiveStripRepresentative_pairing (hε : 0<ε) (F : CubicThetaPositiveStripL2 ε)
    (h : Eisenstein) (W : CompactlySupportedContinuousMap ℝ ℂ) :
    inner ℂ (cubicThetaPositiveStripFourierTest hε h W) F=
      ∫ v in Ioi ε,star (W v)/(v:ℂ)^3*
        ∫ z in cubicThetaHorizontalCell,
          star (Real.fourierChar (tracePair z (cubicThetaRowFrequency h)):ℂ)*
            cubicThetaPositiveStripRepresentative F (z,v) := by
  have hi : IntegrableOn (fun p : CubicThetaPoint =>
      star (W p.val.2*(Real.fourierChar (tracePair p.val.1 (cubicThetaRowFrequency h)):ℂ))*
        cubicThetaPositiveStripRepresentative F (cubicThetaPointCoordinates p))
      (cubicThetaCuspStrip ε) cubicThetaPointMeasure := by
    simpa only [cubicThetaPositiveStripRepresentative_coordinates] using
      cubicThetaPositiveStripRepresentative_pair_integrable hε F h W
  have he := cubicThetaPositiveCuspStrip_fubini hε.le
    (fun y => star (W y.2*(Real.fourierChar (tracePair y.1 (cubicThetaRowFrequency h)):ℂ))*
      cubicThetaPositiveStripRepresentative F y) hi
  change (∫ p in cubicThetaCuspStrip ε,
    star (W p.val.2*(Real.fourierChar (tracePair p.val.1 (cubicThetaRowFrequency h)):ℂ))*
      cubicThetaPositiveStripRepresentative F (cubicThetaPointCoordinates p) ∂cubicThetaPointMeasure)=_ at he
  rw [L2.inner_def]
  calc
    _ = ∫ p in cubicThetaCuspStrip ε,
        star (W p.val.2*(Real.fourierChar (tracePair p.val.1 (cubicThetaRowFrequency h)):ℂ))*
          cubicThetaPositiveStripRepresentative F (cubicThetaPointCoordinates p) ∂cubicThetaPointMeasure := by
      apply integral_congr_ae
      filter_upwards [(cubicThetaPositiveFourierWeight_memLp hε h W).coeFn_toLp] with p hp
      change inner ℂ (((cubicThetaPositiveFourierWeight_memLp hε h W).toLp _) p) (F p)=_
      rw [hp,cubicThetaPositiveStripRepresentative_coordinates,RCLike.inner_apply]
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
