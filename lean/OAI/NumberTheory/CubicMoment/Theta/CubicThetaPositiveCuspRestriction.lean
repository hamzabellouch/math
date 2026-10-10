import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPositiveStripBound
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCuspRestriction
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaStripFiniteVolume

namespace OAI

/-! Actual bounded restriction to any positive-height period strip.
Injectivity is replaced by the proved finite multiplicity below height two. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace CubicFirstMoment

abbrev CubicThetaPositiveStripL2 (ε : ℝ) :=
  Lp ℂ 2 (cubicThetaPointMeasure.restrict (cubicThetaCuspStrip ε))

lemma cubicThetaPositiveStrip_finite {ε : ℝ} (hε : 0<ε) :
    IsFiniteMeasure (cubicThetaPointMeasure.restrict (cubicThetaCuspStrip ε)) := by
  obtain ⟨K,hK,hcover⟩ := cubicThetaPositiveStrip_compact_cover hε
  constructor
  rw [Measure.restrict_apply_univ]
  exact (measure_mono hcover).trans_lt
    ((measure_union_le K (cubicThetaCuspStrip 2)).trans_lt
      (ENNReal.add_lt_top.mpr ⟨cubicThetaPointMeasure_compact hK,
        by simpa only [Measure.restrict_apply_univ] using
          (measure_lt_top (cubicThetaPointMeasure.restrict (cubicThetaCuspStrip 2)) univ)⟩))

lemma cubicThetaFiniteEnergy_positiveStrip_memLp {ε : ℝ} (hε : 0<ε)
    (F : cubicThetaFiniteEnergySections) :
    MemLp (fun p : CubicThetaPoint => F.val.val p) 2
      (cubicThetaPointMeasure.restrict (cubicThetaCuspStrip ε)) := by
  obtain ⟨N,_,hN⟩ := cubicThetaPositiveStrip_pullback_bound hε
  have h := ((cubicThetaFiniteEnergy_norm_integrable F).smul_measure
    (c:=(N:ℝ≥0∞)) (by simp)).mono_measure hN
  have hi := h.comp_measurable cubicThetaQuotientMap_open.continuous.measurable
  apply (memLp_two_iff_integrable_sq_norm F.val.val.continuous.aestronglyMeasurable).mpr
  simpa only [Function.comp_def,cubicThetaSectionNorm_apply] using hi

def cubicThetaFinitePositiveCuspRestriction {ε : ℝ} (hε : 0<ε) :
    cubicThetaFiniteEnergySections →ₗ[ℂ] CubicThetaPositiveStripL2 ε where
  toFun F := (cubicThetaFiniteEnergy_positiveStrip_memLp hε F).toLp _
  map_add' F G := MemLp.toLp_add
    (cubicThetaFiniteEnergy_positiveStrip_memLp hε F)
    (cubicThetaFiniteEnergy_positiveStrip_memLp hε G)
  map_smul' c F := MemLp.toLp_const_smul c
    (cubicThetaFiniteEnergy_positiveStrip_memLp hε F)

lemma cubicThetaFinitePositiveCuspRestriction_norm_sq {ε : ℝ} (hε : 0<ε)
    (F : cubicThetaFiniteEnergySections) :
    ‖cubicThetaFinitePositiveCuspRestriction hε F‖^2=
      ∫ p in cubicThetaCuspStrip ε,‖F.val.val p‖^2 ∂cubicThetaPointMeasure := by
  rw [cubicTheta_l2_norm_sq_measure]
  apply integral_congr_ae
  filter_upwards [(cubicThetaFiniteEnergy_positiveStrip_memLp hε F).coeFn_toLp] with p hp
  change ‖((cubicThetaFiniteEnergy_positiveStrip_memLp hε F).toLp _) p‖^2=_
  rw [hp]

lemma cubicThetaFinitePositiveCuspRestriction_bound {ε : ℝ} (hε : 0<ε) :
    ∃ C,∀ F : cubicThetaFiniteEnergySections,
      ‖cubicThetaFinitePositiveCuspRestriction hε F‖≤
        C*‖cubicThetaFiniteEnergyEmbedding F‖ := by
  obtain ⟨N,_,hN⟩ := cubicThetaPositiveStrip_pullback_bound hε
  refine ⟨Real.sqrt N,fun F => ?_⟩
  have hf := (cubicThetaFiniteEnergy_norm_integrable F).smul_measure
    (c:=(N:ℝ≥0∞)) (by simp)
  have hi := integral_mono_measure hN
    (ae_of_all _ (fun q => sq_nonneg (cubicThetaSectionNorm F q))) hf
  rw [integral_map cubicThetaQuotientMap_open.continuous.measurable.aemeasurable
    (hf.aestronglyMeasurable.mono_measure hN),integral_smul_measure] at hi
  simp only [cubicThetaSectionNorm_apply,ENNReal.toReal_natCast,
    smul_eq_mul] at hi
  rw [←cubicThetaFinitePositiveCuspRestriction_norm_sq hε,
    ←cubicThetaFiniteEnergyValue_norm_sq] at hi
  have hs : (Real.sqrt N*‖cubicThetaFiniteEnergyValue F‖)^2=
      N*‖cubicThetaFiniteEnergyValue F‖^2 := by
    rw [mul_pow,Real.sq_sqrt (Nat.cast_nonneg N)]
  have hb : ‖cubicThetaFinitePositiveCuspRestriction hε F‖≤
      Real.sqrt N*‖cubicThetaFiniteEnergyValue F‖ :=
    _root_.le_of_sq_le_sq (hi.trans_eq hs.symm)
      (mul_nonneg (Real.sqrt_nonneg N) (_root_.norm_nonneg _))
  apply hb.trans
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg N)
  exact cubicThetaGlobalInclusion_bound (cubicThetaFiniteEnergyEmbedding F)

local instance positiveCuspRestriction_finiteEnergyAdd : AddCommGroup cubicThetaFiniteEnergySections :=
  Module.addCommMonoidToAddCommGroup ℂ

def cubicThetaPositiveCuspRestriction {ε : ℝ} (hε : 0<ε) :
    cubicThetaGlobalEnergySpace →L[ℂ] CubicThetaPositiveStripL2 ε :=
  LinearMap.extendOfNorm (𝕜:=ℂ) (𝕜₂:=ℂ) (σ₁₂:=RingHom.id ℂ)
    (E:=cubicThetaFiniteEnergySections) (Eₗ:=cubicThetaGlobalEnergySpace)
    (F:=CubicThetaPositiveStripL2 ε)
    (cubicThetaFinitePositiveCuspRestriction hε) cubicThetaFiniteEnergyEmbedding

lemma cubicThetaPositiveCuspRestriction_finiteEnergy {ε : ℝ} (hε : 0<ε)
    (F : cubicThetaFiniteEnergySections) :
    cubicThetaPositiveCuspRestriction hε (cubicThetaFiniteEnergyEmbedding F)=
      cubicThetaFinitePositiveCuspRestriction hε F :=
  LinearMap.extendOfNorm_eq (𝕜:=ℂ) (𝕜₂:=ℂ) (σ₁₂:=RingHom.id ℂ)
    (f:=cubicThetaFinitePositiveCuspRestriction hε) (e:=cubicThetaFiniteEnergyEmbedding)
    cubicThetaFiniteEnergyEmbedding_dense (cubicThetaFinitePositiveCuspRestriction_bound hε) F

end CubicFirstMoment

end

end OAI
