import OAI.NumberTheory.CubicMoment.Theta.CubicThetaBorelTransport
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPositiveModelIdentity

namespace OAI

/-! The completed positive-strip restriction is the actual measurable
lift from the quotient, including its cubic automorphy factor. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace CubicFirstMoment

lemma cubicThetaPositiveStrip_pull_ae {ε : ℝ} (hε : 0<ε)
    {P : CubicThetaQuotient → Prop} (hP : ∀ᵐ q ∂cubicThetaQuotientMeasure,P q) :
    ∀ᵐ p ∂cubicThetaPointMeasure.restrict (cubicThetaCuspStrip ε),P (cubicThetaQuotientMap p) := by
  obtain ⟨N,hNpos,hN⟩ := cubicThetaPositiveStrip_pullback_bound hε
  have hNne : (N:ℝ≥0∞)≠0 := by exact_mod_cast hNpos.ne'
  have hs : ∀ᵐ q ∂(N:ℝ≥0∞) • cubicThetaQuotientMeasure,P q :=
    (Measure.ae_ennreal_smul_measure_iff hNne).mpr hP
  exact ae_of_ae_map cubicThetaQuotientMap_open.continuous.measurable.aemeasurable
    (ae_mono hN hs)

def cubicThetaBorelRestrictionLinear {ε : ℝ} (hε : 0<ε) :
    CubicThetaGlobalL2 →ₗ[ℂ] CubicThetaPositiveStripL2 ε where
  toFun F := (cubicThetaBorelLift_positive_memLp hε (Lp.stronglyMeasurable F).measurable
    (Lp.memLp F)).toLp _
  map_add' F G := by
    apply Lp.ext
    filter_upwards [
      (cubicThetaBorelLift_positive_memLp hε (Lp.stronglyMeasurable (F+G)).measurable
        (Lp.memLp (F+G))).coeFn_toLp,
      (cubicThetaBorelLift_positive_memLp hε (Lp.stronglyMeasurable F).measurable
        (Lp.memLp F)).coeFn_toLp,
      (cubicThetaBorelLift_positive_memLp hε (Lp.stronglyMeasurable G).measurable
        (Lp.memLp G)).coeFn_toLp,
      Lp.coeFn_add
        ((cubicThetaBorelLift_positive_memLp hε (Lp.stronglyMeasurable F).measurable
          (Lp.memLp F)).toLp _)
        ((cubicThetaBorelLift_positive_memLp hε (Lp.stronglyMeasurable G).measurable
          (Lp.memLp G)).toLp _),
      cubicThetaPositiveStrip_pull_ae hε (Lp.coeFn_add F G)] with p hFG hF hG hadd hq
    change ((cubicThetaBorelLift_positive_memLp hε
      (Lp.stronglyMeasurable (F+G)).measurable (Lp.memLp (F+G))).toLp _) p=_
    rw [hFG,hadd]
    simp only [Pi.add_apply]
    rw [hF,hG]
    simp only [cubicThetaBorelLift,Pi.add_apply] at hq ⊢
    rw [hq,mul_add]
  map_smul' c F := by
    apply Lp.ext
    filter_upwards [
      (cubicThetaBorelLift_positive_memLp hε (Lp.stronglyMeasurable (c • F)).measurable
        (Lp.memLp (c • F))).coeFn_toLp,
      (cubicThetaBorelLift_positive_memLp hε (Lp.stronglyMeasurable F).measurable
        (Lp.memLp F)).coeFn_toLp,
      Lp.coeFn_smul c ((cubicThetaBorelLift_positive_memLp hε
        (Lp.stronglyMeasurable F).measurable (Lp.memLp F)).toLp _),
      cubicThetaPositiveStrip_pull_ae hε (Lp.coeFn_smul c F)] with p hCF hF hsm hq
    change ((cubicThetaBorelLift_positive_memLp hε
      (Lp.stronglyMeasurable (c • F)).measurable (Lp.memLp (c • F))).toLp _) p=_
    simp only [RingHom.id_apply]
    rw [hCF,hsm]
    simp only [Pi.smul_apply]
    rw [hF]
    simp only [cubicThetaBorelLift,Pi.smul_apply,smul_eq_mul] at hq ⊢
    rw [hq]
    ring

lemma cubicThetaBorelRestrictionLinear_bound {ε : ℝ} (hε : 0<ε) :
    ∃ C,∀ F : CubicThetaGlobalL2,‖cubicThetaBorelRestrictionLinear hε F‖≤C*‖F‖ := by
  obtain ⟨N,_,hN⟩ := cubicThetaPositiveStrip_pullback_bound hε
  refine ⟨Real.sqrt N,fun F => ?_⟩
  have hf := ((Lp.memLp F).integrable_norm_pow (by norm_num)).smul_measure
    (c:=(N:ℝ≥0∞)) (by simp)
  have hi := integral_mono_measure hN (ae_of_all _ (fun q => sq_nonneg ‖F q‖)) hf
  rw [integral_map cubicThetaQuotientMap_open.continuous.measurable.aemeasurable
    (hf.aestronglyMeasurable.mono_measure hN),integral_smul_measure] at hi
  simp only [ENNReal.toReal_natCast,smul_eq_mul] at hi
  rw [←cubicTheta_l2_norm_sq_measure F] at hi
  have he : ‖cubicThetaBorelRestrictionLinear hε F‖^2=
      ∫ p in cubicThetaCuspStrip ε,‖F (cubicThetaQuotientMap p)‖^2 ∂cubicThetaPointMeasure := by
    rw [cubicTheta_l2_norm_sq_measure]
    apply integral_congr_ae
    filter_upwards [(cubicThetaBorelLift_positive_memLp hε
      (Lp.stronglyMeasurable F).measurable (Lp.memLp F)).coeFn_toLp] with p hp
    change ‖((cubicThetaBorelLift_positive_memLp hε
      (Lp.stronglyMeasurable F).measurable (Lp.memLp F)).toLp _) p‖^2=_
    rw [hp,cubicThetaBorelLift_norm]
  rw [←he] at hi
  have hs : (Real.sqrt N*‖F‖)^2=N*‖F‖^2 := by
    rw [mul_pow,Real.sq_sqrt (Nat.cast_nonneg N)]
  exact _root_.le_of_sq_le_sq (hi.trans_eq hs.symm)
    (mul_nonneg (Real.sqrt_nonneg N) (_root_.norm_nonneg F))

def cubicThetaBorelRestriction {ε : ℝ} (hε : 0<ε) :
    CubicThetaGlobalL2 →L[ℂ] CubicThetaPositiveStripL2 ε :=
  (cubicThetaBorelRestrictionLinear hε).mkContinuousOfExistsBound
    (cubicThetaBorelRestrictionLinear_bound hε)

lemma cubicThetaBorelRestriction_coe {ε : ℝ} (hε : 0<ε) (F : CubicThetaGlobalL2) :
    cubicThetaBorelRestriction hε F =ᵐ[cubicThetaPointMeasure.restrict (cubicThetaCuspStrip ε)]
      cubicThetaBorelLift (F : CubicThetaQuotient → ℂ) :=
  (cubicThetaBorelLift_positive_memLp hε
    (Lp.stronglyMeasurable F).measurable (Lp.memLp F)).coeFn_toLp

lemma cubicThetaBorelRestriction_finite {ε : ℝ} (hε : 0<ε)
    (F : cubicThetaFiniteEnergySections) :
    cubicThetaBorelRestriction hε (cubicThetaFiniteEnergyValue F)=
      cubicThetaFinitePositiveCuspRestriction hε F := by
  apply Lp.ext
  filter_upwards [cubicThetaBorelRestriction_coe hε (cubicThetaFiniteEnergyValue F),
    (cubicThetaFiniteEnergy_positiveStrip_memLp hε F).coeFn_toLp,
    cubicThetaPositiveStrip_pull_ae hε F.property.2.1.coeFn_toLp] with p hB hF hq
  change (cubicThetaFiniteEnergyValue F) (cubicThetaQuotientMap p)=
    cubicThetaSectionRepresentative F (cubicThetaQuotientMap p) at hq
  change _=((cubicThetaFiniteEnergy_positiveStrip_memLp hε F).toLp _) p
  rw [hB,hF,cubicThetaBorelLift,hq]
  exact cubicThetaBorelLift_section F p

theorem cubicThetaPositiveCuspRestriction_borel {ε : ℝ} (hε : 0<ε)
    (u : cubicThetaGlobalEnergySpace) :
    cubicThetaPositiveCuspRestriction hε u=
      cubicThetaBorelRestriction hε (cubicThetaGlobalInclusion u) := by
  refine cubicThetaFiniteEnergyEmbedding_dense.induction_on u
    (isClosed_eq (cubicThetaPositiveCuspRestriction hε).continuous
      ((cubicThetaBorelRestriction hε).continuous.comp cubicThetaGlobalInclusion.continuous)) ?_
  intro F
  rw [cubicThetaPositiveCuspRestriction_finiteEnergy,cubicThetaFiniteEnergyEmbedding_value,
    cubicThetaBorelRestriction_finite]

theorem cubicThetaResidue_borel_model {ε : ℝ} (hε : 0<ε) :
    cubicThetaBorelLift (cubicThetaGlobalInclusion cubicThetaNormalizedArithmeticResidue)
      =ᵐ[cubicThetaPointMeasure.restrict (cubicThetaCuspStrip ε)]
        (fun p => cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar p.val) := by
  have he := cubicThetaPositiveModelIdentity hε
  rw [cubicThetaPositiveCuspRestriction_borel] at he
  filter_upwards [cubicThetaBorelRestriction_coe hε
    (cubicThetaGlobalInclusion cubicThetaNormalizedArithmeticResidue),
    (cubicThetaArithmeticModel_positive_memLp cubicThetaArithmeticBaseScalar hε).coeFn_toLp] with p hB hM
  rw [←hB,he]
  exact hM

end CubicFirstMoment

end

end OAI
