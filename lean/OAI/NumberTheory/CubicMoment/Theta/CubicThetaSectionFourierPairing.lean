import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeBranchFourier
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaSectionMeanPairing

namespace OAI

/-! Actual weighted observations at every horizontal frequency, obtained
by Fubini on the geometric cusp strip. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported
namespace CubicFirstMoment

def cubicThetaSectionFourierFunction (F : CubicThetaSection) (h : Eisenstein) (v : ℝ) : ℂ :=
  cubicThetaHorizontalFourierCoefficient h (fun z => cubicThetaSectionFunction F (z,v))

lemma cubicThetaSectionFourierFunction_eq (F : CubicThetaSection) (h : Eisenstein)
    (v : ℝ) (hv : 0<v) :
    cubicThetaSectionFourierFunction F h v=cubicThetaSectionFourier F v hv h := by
  unfold cubicThetaSectionFourierFunction cubicThetaSectionFourier
  congr 1
  funext z
  exact cubicThetaSectionFunction_apply F hv

lemma cubicThetaSectionFourierPairing_integrable (F : cubicThetaFiniteEnergySections)
    (h : Eisenstein) (W : C_c(ℝ,ℂ)) :
    IntegrableOn (fun p : CubicThetaPoint =>
      star (W p.val.2*cubicThetaHorizontalCharacter h p.val.1)*F.val.val p)
      (cubicThetaCuspStrip 2) cubicThetaPointMeasure := by
  have hi := L2.integrable_inner (𝕜:=ℂ) (cubicThetaCuspFourierTest h W)
    (cubicThetaFiniteCuspRestriction F)
  apply hi.congr
  filter_upwards [(cubicThetaCuspFourierWeight_memLp h W).coeFn_toLp,
    (cubicThetaFiniteEnergy_strip_memLp F).coeFn_toLp] with p hW hF
  change inner ℂ (((cubicThetaCuspFourierWeight_memLp h W).toLp _) p)
    (((cubicThetaFiniteEnergy_strip_memLp F).toLp _) p)=_
  rw [hW,hF]
  simpa only [starRingEnd_apply,cubicThetaCuspFourierWeight,cubicThetaHorizontalCharacter] using
    (RCLike.inner_apply' (cubicThetaCuspFourierWeight h W p) (F.val.val p))

theorem cubicThetaSectionFourierPairing (F : cubicThetaFiniteEnergySections)
    (h : Eisenstein) (W : C_c(ℝ,ℂ)) :
    inner ℂ (cubicThetaCuspFourierTest h W) (cubicThetaFiniteCuspRestriction F)=
      ∫ v in Ioi (2:ℝ),star (W v)/(v:ℂ)^3*cubicThetaSectionFourierFunction F h v := by
  have hi := cubicThetaSectionFourierPairing_integrable F h W
  have hi' : IntegrableOn (fun p : CubicThetaPoint =>
      star (W p.val.2*cubicThetaHorizontalCharacter h p.val.1)*
        cubicThetaSectionFunction F p.val)
      (cubicThetaCuspStrip 2) cubicThetaPointMeasure := by
    apply hi.congr
    filter_upwards with p
    rw [cubicThetaSectionFunction_coordinates]
  have he := cubicThetaCuspStrip_fubini
    (fun y => star (W y.2*cubicThetaHorizontalCharacter h y.1)*
      cubicThetaSectionFunction F y) hi'
  have hpair : inner ℂ (cubicThetaCuspFourierTest h W) (cubicThetaFiniteCuspRestriction F)=
      ∫ p in cubicThetaCuspStrip 2,
        star (W p.val.2*cubicThetaHorizontalCharacter h p.val.1)*
          cubicThetaSectionFunction F p.val ∂cubicThetaPointMeasure := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(cubicThetaCuspFourierWeight_memLp h W).coeFn_toLp,
      (cubicThetaFiniteEnergy_strip_memLp F).coeFn_toLp] with p hW hF
    change inner ℂ (((cubicThetaCuspFourierWeight_memLp h W).toLp _) p)
      (((cubicThetaFiniteEnergy_strip_memLp F).toLp _) p)=_
    rw [hW,hF,cubicThetaSectionFunction_coordinates]
    simpa only [starRingEnd_apply,cubicThetaCuspFourierWeight,cubicThetaHorizontalCharacter] using
      (RCLike.inner_apply' (cubicThetaCuspFourierWeight h W p) (F.val.val p))
  change (∫ p in cubicThetaCuspStrip 2,
    star (W p.val.2*cubicThetaHorizontalCharacter h p.val.1)*
      cubicThetaSectionFunction F p.val ∂cubicThetaPointMeasure)=
    ∫ v in Ioi (2:ℝ),∫ z in cubicThetaHorizontalCell,
      star (W v*cubicThetaHorizontalCharacter h z)*cubicThetaSectionFunction F (z,v)/(v:ℂ)^3 at he
  rw [hpair,he]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro v _
  dsimp only [cubicThetaSectionFourierFunction,cubicThetaHorizontalFourierCoefficient]
  rw [←integral_const_mul]
  apply setIntegral_congr_fun cubicThetaHorizontalCell_measurable
  intro z _
  simp only [star_mul]
  ring

lemma cubicThetaSectionFourier_weight_integrable (F : cubicThetaFiniteEnergySections)
    (h : Eisenstein) (W : C_c(ℝ,ℂ)) :
    IntegrableOn (fun v => star (W v)/(v:ℂ)^3*cubicThetaSectionFourierFunction F h v)
      (Ioi (2:ℝ)) := by
  have hi := cubicThetaSectionFourierPairing_integrable F h W
  have hi' : IntegrableOn (fun p : CubicThetaPoint =>
      star (W p.val.2*cubicThetaHorizontalCharacter h p.val.1)*
        cubicThetaSectionFunction F p.val)
      (cubicThetaCuspStrip 2) cubicThetaPointMeasure := by
    apply hi.congr
    filter_upwards with p
    rw [cubicThetaSectionFunction_coordinates]
  have hi'' := (cubicThetaPointIntegrable_complex_density (cubicThetaCuspStrip_measurable 2)
    (fun y => star (W y.2*cubicThetaHorizontalCharacter h y.1)*
      cubicThetaSectionFunction F y)).mp hi'
  rw [cubicThetaCuspStrip_coordinates (by norm_num : (0:ℝ)≤2)] at hi''
  change Integrable (fun y : ℂ × ℝ => star (W y.2*cubicThetaHorizontalCharacter h y.1)*
    cubicThetaSectionFunction F y/(y.2:ℂ)^3)
    (((volume : Measure ℂ).prod (volume : Measure ℝ)).restrict _) at hi''
  rw [←Measure.prod_restrict] at hi''
  apply hi''.integral_prod_right.congr
  filter_upwards with v
  dsimp only [cubicThetaSectionFourierFunction,cubicThetaHorizontalFourierCoefficient]
  rw [←integral_const_mul]
  apply setIntegral_congr_fun cubicThetaHorizontalCell_measurable
  intro z _
  simp only [star_mul]
  ring

end CubicFirstMoment

end

end OAI
