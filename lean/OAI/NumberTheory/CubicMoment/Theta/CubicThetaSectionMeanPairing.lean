import OAI.NumberTheory.CubicMoment.Theta.CubicThetaSectionMean
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCuspFourierIntegral
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeFiniteEnergy

namespace OAI

/-! Genuine compact radial observations of finite-energy sections, expressed
through their scalar horizontal means. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported
namespace CubicFirstMoment

lemma cubicThetaSectionMeanPairing_integrable (F : cubicThetaFiniteEnergySections)
    (W : C_c(ℝ,ℂ)) :
    IntegrableOn (fun p : CubicThetaPoint => star (W p.val.2)*F.val.val p)
      (cubicThetaCuspStrip 2) cubicThetaPointMeasure := by
  have hi := L2.integrable_inner (𝕜:=ℂ) (cubicThetaCuspFourierTest 0 W)
    (cubicThetaFiniteCuspRestriction F)
  apply hi.congr
  filter_upwards [(cubicThetaCuspFourierWeight_memLp 0 W).coeFn_toLp,
    (cubicThetaFiniteEnergy_strip_memLp F).coeFn_toLp] with p hW hF
  change inner ℂ (((cubicThetaCuspFourierWeight_memLp 0 W).toLp _) p)
    (((cubicThetaFiniteEnergy_strip_memLp F).toLp _) p)=_
  rw [hW,hF]
  rw [show cubicThetaCuspFourierWeight 0 W p=W p.val.2 from by
    simp [cubicThetaCuspFourierWeight,cubicThetaRowFrequency,tracePair]]
  simpa only [starRingEnd_apply] using (RCLike.inner_apply' (W p.val.2) (F.val.val p))

lemma cubicThetaSectionMeanPairing (F : cubicThetaFiniteEnergySections) (W : C_c(ℝ,ℂ)) :
    inner ℂ (cubicThetaCuspFourierTest 0 W) (cubicThetaFiniteCuspRestriction F)=
      ∫ v in Ioi (2:ℝ),star (W v)/(v:ℂ)^3*cubicThetaSectionMean F v := by
  have hi := cubicThetaSectionMeanPairing_integrable F W
  have hi' : IntegrableOn (fun p : CubicThetaPoint =>
      star (W p.val.2)*cubicThetaSectionFunction F p.val)
      (cubicThetaCuspStrip 2) cubicThetaPointMeasure := by
    apply hi.congr
    filter_upwards with p
    rw [cubicThetaSectionFunction_coordinates]
  have he := cubicThetaCuspStrip_fubini
    (fun y => star (W y.2)*cubicThetaSectionFunction F y) hi'
  have hpair : inner ℂ (cubicThetaCuspFourierTest 0 W) (cubicThetaFiniteCuspRestriction F)=
      ∫ p in cubicThetaCuspStrip 2,star (W p.val.2)*cubicThetaSectionFunction F p.val
        ∂cubicThetaPointMeasure := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(cubicThetaCuspFourierWeight_memLp 0 W).coeFn_toLp,
      (cubicThetaFiniteEnergy_strip_memLp F).coeFn_toLp] with p hW hF
    change inner ℂ (((cubicThetaCuspFourierWeight_memLp 0 W).toLp _) p)
      (((cubicThetaFiniteEnergy_strip_memLp F).toLp _) p)=_
    rw [hW,hF,cubicThetaSectionFunction_coordinates]
    rw [show cubicThetaCuspFourierWeight 0 W p=W p.val.2 from by
      simp [cubicThetaCuspFourierWeight,cubicThetaRowFrequency,tracePair]]
    simpa only [starRingEnd_apply] using (RCLike.inner_apply' (W p.val.2) (F.val.val p))
  change (∫ p in cubicThetaCuspStrip 2,star (W p.val.2)*cubicThetaSectionFunction F p.val
    ∂cubicThetaPointMeasure)=
    ∫ v in Ioi (2:ℝ),∫ z in cubicThetaHorizontalCell,
      star (W v)*cubicThetaSectionFunction F (z,v)/(v:ℂ)^3 at he
  rw [hpair]
  refine he.trans ?_
  apply setIntegral_congr_fun measurableSet_Ioi
  intro v _
  dsimp only [cubicThetaSectionMean]
  rw [←integral_const_mul]
  apply setIntegral_congr_fun cubicThetaHorizontalCell_measurable
  intro z _
  ring

theorem cubicThetaSectionMeanPairing_hecke {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaFiniteEnergySections) (W : C_c(ℝ,ℂ)) :
    inner ℂ (cubicThetaCuspFourierTest 0 W)
      (cubicThetaFiniteCuspRestriction (cubicThetaPrimeCubeHeckeFinite hp F))=
      ∫ v in Ioi (2:ℝ),star (W v)/(v:ℂ)^3*
        (cubicThetaSectionMean F (‖(p:ℂ)‖^3*v)+
          (norm (p^3):ℂ)*cubicThetaSectionMean F (v/‖(p:ℂ)‖^3)) := by
  rw [cubicThetaSectionMeanPairing]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro v hv
  have hv' : 0<v := lt_trans (by norm_num) hv
  change star (W v)/(v:ℂ)^3*cubicThetaSectionMean (cubicThetaPrimeCubeHecke hp F) v=_
  rw [cubicThetaSectionMean_hecke hp _ v hv']

end CubicFirstMoment

end

end OAI
