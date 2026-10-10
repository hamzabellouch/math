import OAI.NumberTheory.CubicMoment.Theta.CubicThetaInvertedIncoming

namespace OAI

/-! L2 bounds for the literal inverted restriction of finite-energy
sections. Only the value norm is needed for this transport. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaSectionL2_norm_sq (F : CubicThetaSection)
    (hF : MemLp (cubicThetaSectionRepresentative F) 2 cubicThetaQuotientMeasure) :
    ‖hF.toLp (cubicThetaSectionRepresentative F)‖^2=
      ∫ q, cubicThetaSectionNorm F q^2 ∂cubicThetaQuotientMeasure := by
  rw [cubicTheta_l2_norm_sq_measure]
  apply integral_congr_ae
  filter_upwards [hF.coeFn_toLp] with q hq
  rw [hq,cubicThetaSectionRepresentative_norm]

lemma cubicThetaInversionSection_L2_norm (F : CubicThetaSection)
    (hF : MemLp (cubicThetaSectionRepresentative F) 2 cubicThetaQuotientMeasure) :
    ‖(cubicThetaInversionSection_memLp F hF).toLp
        (cubicThetaSectionRepresentative (cubicThetaInversionSection F))‖=
      ‖hF.toLp (cubicThetaSectionRepresentative F)‖ := by
  apply (sq_eq_sq₀ (_root_.norm_nonneg _) (_root_.norm_nonneg _)).mp
  rw [cubicThetaSectionL2_norm_sq,cubicThetaSectionL2_norm_sq]
  calc
    _ = ∫ q, cubicThetaSectionNorm F
        (cubicThetaIntegralQuotientMap cubicThetaFullInversion q)^2 ∂cubicThetaQuotientMeasure := by
      apply integral_congr_ae
      filter_upwards with q
      rw [cubicThetaInversionSection_norm]
    _ = _ := (cubicThetaIntegralQuotient_measurePreserving cubicThetaFullInversion).integral_comp
      (cubicThetaIntegralQuotientHomeomorph cubicThetaFullInversion).measurableEmbedding
      (fun q => cubicThetaSectionNorm F q^2)

lemma cubicThetaSectionStrip_norm_le (F : CubicThetaSection)
    (hF : MemLp (cubicThetaSectionRepresentative F) 2 cubicThetaQuotientMeasure) :
    ‖(cubicThetaSection_strip_memLp F hF).toLp (fun p : CubicThetaPoint => F.val p)‖≤
      ‖hF.toLp (cubicThetaSectionRepresentative F)‖ := by
  have hn : Integrable (fun q => cubicThetaSectionNorm F q^2) cubicThetaQuotientMeasure := by
    simpa only [cubicThetaSectionRepresentative_norm] using hF.integrable_norm_pow (by norm_num)
  have hi := cubicThetaInjective_integral_le (cubicThetaCuspStrip_measurable 2)
    (cubicThetaCuspStrip_injective (by norm_num)) hn (fun q => sq_nonneg (cubicThetaSectionNorm F q))
  simp only [cubicThetaSectionNorm_apply] at hi
  have hs : ‖(cubicThetaSection_strip_memLp F hF).toLp (fun p : CubicThetaPoint => F.val p)‖^2=
      ∫ p in cubicThetaCuspStrip 2, ‖F.val p‖^2 ∂cubicThetaPointMeasure := by
    rw [cubicTheta_l2_norm_sq_measure]
    apply integral_congr_ae
    filter_upwards [(cubicThetaSection_strip_memLp F hF).coeFn_toLp] with p hp
    rw [hp]
  rw [←hs,←cubicThetaSectionL2_norm_sq F hF] at hi
  exact _root_.le_of_sq_le_sq hi (_root_.norm_nonneg _)

def cubicThetaInvertedFiniteRestriction : cubicThetaFiniteEnergySections →ₗ[ℂ] CubicThetaStripL2 where
  toFun F := (cubicThetaSection_strip_memLp (cubicThetaInversionSection F)
    (cubicThetaInversionSection_memLp F F.property.2.1)).toLp _
  map_add' _F _G := MemLp.toLp_add _ _
  map_smul' c _F := MemLp.toLp_const_smul c _

lemma cubicThetaInvertedFiniteRestriction_bound (F : cubicThetaFiniteEnergySections) :
    ‖cubicThetaInvertedFiniteRestriction F‖≤‖cubicThetaFiniteEnergyValue F‖ := by
  exact (cubicThetaSectionStrip_norm_le (cubicThetaInversionSection F)
    (cubicThetaInversionSection_memLp F F.property.2.1)).trans_eq
      (cubicThetaInversionSection_L2_norm F F.property.2.1)

end CubicFirstMoment

end

end OAI
