import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFiniteEnergySections
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCuspStripMeasure

namespace OAI

/-! Restriction of actual finite-energy sections to the injective
height-two cusp strip is bounded in L2 by the global value norm. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

abbrev CubicThetaStripL2 := Lp ℂ 2 (cubicThetaPointMeasure.restrict (cubicThetaCuspStrip 2))

lemma cubicThetaFiniteEnergy_norm_integrable (F : cubicThetaFiniteEnergySections) :
    Integrable (fun q => cubicThetaSectionNorm F q^2) cubicThetaQuotientMeasure := by
  simpa only [cubicThetaSectionRepresentative_norm] using
    F.property.2.1.integrable_norm_pow (by norm_num)

lemma cubicThetaFiniteEnergy_strip_memLp (F : cubicThetaFiniteEnergySections) :
    MemLp (fun p : CubicThetaPoint => F.val.val p) 2
      (cubicThetaPointMeasure.restrict (cubicThetaCuspStrip 2)) := by
  apply (memLp_two_iff_integrable_sq_norm F.val.val.continuous.aestronglyMeasurable).mpr
  have h := (cubicThetaFiniteEnergy_norm_integrable F).integrableOn
    (s:=cubicThetaQuotientMap '' cubicThetaCuspStrip 2)
  unfold IntegrableOn at h
  rw [← cubicThetaInjective_map_restrict (cubicThetaCuspStrip_measurable 2)
    (cubicThetaCuspStrip_injective (by norm_num))] at h
  have hi := h.comp_measurable cubicThetaQuotientMap_open.continuous.measurable
  simpa only [Function.comp_def,cubicThetaSectionNorm_apply] using hi

def cubicThetaFiniteCuspRestriction : cubicThetaFiniteEnergySections →ₗ[ℂ] CubicThetaStripL2 where
  toFun F := (cubicThetaFiniteEnergy_strip_memLp F).toLp _
  map_add' F G := MemLp.toLp_add (cubicThetaFiniteEnergy_strip_memLp F) (cubicThetaFiniteEnergy_strip_memLp G)
  map_smul' c F := MemLp.toLp_const_smul c (cubicThetaFiniteEnergy_strip_memLp F)

lemma cubicThetaFiniteCuspRestriction_norm_sq (F : cubicThetaFiniteEnergySections) :
    ‖cubicThetaFiniteCuspRestriction F‖^2=
      ∫ p in cubicThetaCuspStrip 2, ‖F.val.val p‖^2 ∂cubicThetaPointMeasure := by
  rw [cubicTheta_l2_norm_sq_measure]
  apply integral_congr_ae
  filter_upwards [(cubicThetaFiniteEnergy_strip_memLp F).coeFn_toLp] with p hp
  change ‖((cubicThetaFiniteEnergy_strip_memLp F).toLp _) p‖^2=_
  rw [hp]

lemma cubicThetaFiniteEnergyValue_norm_sq (F : cubicThetaFiniteEnergySections) :
    ‖cubicThetaFiniteEnergyValue F‖^2=
      ∫ q, cubicThetaSectionNorm F q^2 ∂cubicThetaQuotientMeasure := by
  rw [cubicTheta_l2_norm_sq_measure]
  apply integral_congr_ae
  filter_upwards [F.property.2.1.coeFn_toLp] with q hq
  change ‖(F.property.2.1.toLp _) q‖^2=_
  rw [hq,cubicThetaSectionRepresentative_norm]

lemma cubicThetaFiniteCuspRestriction_bound (F : cubicThetaFiniteEnergySections) :
    ‖cubicThetaFiniteCuspRestriction F‖≤‖cubicThetaFiniteEnergyValue F‖ := by
  have hi := cubicThetaInjective_integral_le (cubicThetaCuspStrip_measurable 2)
    (cubicThetaCuspStrip_injective (by norm_num)) (cubicThetaFiniteEnergy_norm_integrable F)
    (fun q => sq_nonneg (cubicThetaSectionNorm F q))
  simp only [cubicThetaSectionNorm_apply] at hi
  rw [← cubicThetaFiniteCuspRestriction_norm_sq,← cubicThetaFiniteEnergyValue_norm_sq] at hi
  nlinarith [_root_.norm_nonneg (cubicThetaFiniteCuspRestriction F),
    _root_.norm_nonneg (cubicThetaFiniteEnergyValue F)]

end CubicFirstMoment

end

end OAI
