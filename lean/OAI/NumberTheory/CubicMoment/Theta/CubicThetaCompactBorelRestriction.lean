import OAI.NumberTheory.CubicMoment.Theta.CubicThetaBorelTransport

namespace OAI

/-! A bounded compact restriction of the actual global L2 lift. This
permits cusp Fourier windows after arbitrary integral coordinate changes. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace CubicFirstMoment

lemma cubicThetaCompact_pull_ae {K : Set CubicThetaPoint} (hK : IsCompact K)
    {P : CubicThetaQuotient → Prop} (hP : ∀ᵐ q ∂cubicThetaQuotientMeasure,P q) :
    ∀ᵐ p ∂cubicThetaPointMeasure.restrict K,P (cubicThetaQuotientMap p) := by
  obtain ⟨N,hN⟩ := cubicThetaCompact_pullback_bound hK
  have hs : ∀ᵐ q ∂(N:ℝ≥0∞) • cubicThetaQuotientMeasure,P q :=
    Measure.ae_smul_measure hP _
  exact ae_of_ae_map cubicThetaQuotientMap_open.continuous.measurable.aemeasurable
    (ae_mono hN hs)

lemma cubicThetaBorelLift_compact_memLp {K : Set CubicThetaPoint} (hK : IsCompact K)
    {f : CubicThetaQuotient → ℂ} (hm : Measurable f) (hf : MemLp f 2 cubicThetaQuotientMeasure) :
    MemLp (cubicThetaBorelLift f) 2 (cubicThetaPointMeasure.restrict K) := by
  obtain ⟨N,hN⟩ := cubicThetaCompact_pullback_bound hK
  have hi := (hf.integrable_norm_pow (by norm_num)).smul_measure
    (c:=(N:ℝ≥0∞)) (by simp)
  have hc := (hi.mono_measure hN).comp_measurable cubicThetaQuotientMap_open.continuous.measurable
  apply (memLp_two_iff_integrable_sq_norm
    (cubicThetaBorelLift_measurable hm).aestronglyMeasurable).mpr
  simpa only [Function.comp_def,cubicThetaBorelLift_norm] using hc

def cubicThetaCompactBorelRestrictionLinear {K : Set CubicThetaPoint} (hK : IsCompact K) :
    CubicThetaGlobalL2 →ₗ[ℂ] Lp ℂ 2 (cubicThetaPointMeasure.restrict K) where
  toFun F := (cubicThetaBorelLift_compact_memLp hK (Lp.stronglyMeasurable F).measurable
    (Lp.memLp F)).toLp _
  map_add' F G := by
    apply Lp.ext
    filter_upwards [
      (cubicThetaBorelLift_compact_memLp hK (Lp.stronglyMeasurable (F+G)).measurable
        (Lp.memLp (F+G))).coeFn_toLp,
      (cubicThetaBorelLift_compact_memLp hK (Lp.stronglyMeasurable F).measurable
        (Lp.memLp F)).coeFn_toLp,
      (cubicThetaBorelLift_compact_memLp hK (Lp.stronglyMeasurable G).measurable
        (Lp.memLp G)).coeFn_toLp,
      Lp.coeFn_add
        ((cubicThetaBorelLift_compact_memLp hK (Lp.stronglyMeasurable F).measurable
          (Lp.memLp F)).toLp _)
        ((cubicThetaBorelLift_compact_memLp hK (Lp.stronglyMeasurable G).measurable
          (Lp.memLp G)).toLp _),
      cubicThetaCompact_pull_ae hK (Lp.coeFn_add F G)] with p hFG hF hG hadd hq
    change ((cubicThetaBorelLift_compact_memLp hK
      (Lp.stronglyMeasurable (F+G)).measurable (Lp.memLp (F+G))).toLp _) p=_
    rw [hFG,hadd]
    simp only [Pi.add_apply]
    rw [hF,hG]
    simp only [cubicThetaBorelLift,Pi.add_apply] at hq ⊢
    rw [hq,mul_add]
  map_smul' c F := by
    apply Lp.ext
    filter_upwards [
      (cubicThetaBorelLift_compact_memLp hK (Lp.stronglyMeasurable (c • F)).measurable
        (Lp.memLp (c • F))).coeFn_toLp,
      (cubicThetaBorelLift_compact_memLp hK (Lp.stronglyMeasurable F).measurable
        (Lp.memLp F)).coeFn_toLp,
      Lp.coeFn_smul c ((cubicThetaBorelLift_compact_memLp hK
        (Lp.stronglyMeasurable F).measurable (Lp.memLp F)).toLp _),
      cubicThetaCompact_pull_ae hK (Lp.coeFn_smul c F)] with p hCF hF hsm hq
    change ((cubicThetaBorelLift_compact_memLp hK
      (Lp.stronglyMeasurable (c • F)).measurable (Lp.memLp (c • F))).toLp _) p=_
    simp only [RingHom.id_apply]
    rw [hCF,hsm]
    simp only [Pi.smul_apply]
    rw [hF]
    simp only [cubicThetaBorelLift,Pi.smul_apply,smul_eq_mul] at hq ⊢
    rw [hq]
    ring

lemma cubicThetaCompactBorelRestrictionLinear_bound {K : Set CubicThetaPoint} (hK : IsCompact K) :
    ∃ C,∀ F : CubicThetaGlobalL2,‖cubicThetaCompactBorelRestrictionLinear hK F‖≤C*‖F‖ := by
  obtain ⟨N,hN⟩ := cubicThetaCompact_pullback_bound hK
  refine ⟨Real.sqrt N,fun F => ?_⟩
  have hf := ((Lp.memLp F).integrable_norm_pow (by norm_num)).smul_measure
    (c:=(N:ℝ≥0∞)) (by simp)
  have hi := integral_mono_measure hN (ae_of_all _ (fun q => sq_nonneg ‖F q‖)) hf
  rw [integral_map cubicThetaQuotientMap_open.continuous.measurable.aemeasurable
    (hf.aestronglyMeasurable.mono_measure hN),integral_smul_measure] at hi
  simp only [ENNReal.toReal_natCast,smul_eq_mul] at hi
  rw [←cubicTheta_l2_norm_sq_measure F] at hi
  have he : ‖cubicThetaCompactBorelRestrictionLinear hK F‖^2=
      ∫ p in K,‖F (cubicThetaQuotientMap p)‖^2 ∂cubicThetaPointMeasure := by
    rw [cubicTheta_l2_norm_sq_measure]
    apply integral_congr_ae
    filter_upwards [(cubicThetaBorelLift_compact_memLp hK
      (Lp.stronglyMeasurable F).measurable (Lp.memLp F)).coeFn_toLp] with p hp
    change ‖((cubicThetaBorelLift_compact_memLp hK
      (Lp.stronglyMeasurable F).measurable (Lp.memLp F)).toLp _) p‖^2=_
    rw [hp,cubicThetaBorelLift_norm]
  rw [←he] at hi
  have hs : (Real.sqrt N*‖F‖)^2=N*‖F‖^2 := by
    rw [mul_pow,Real.sq_sqrt (Nat.cast_nonneg N)]
  exact _root_.le_of_sq_le_sq (hi.trans_eq hs.symm)
    (mul_nonneg (Real.sqrt_nonneg N) (_root_.norm_nonneg F))

def cubicThetaCompactBorelRestriction {K : Set CubicThetaPoint} (hK : IsCompact K) :
    CubicThetaGlobalL2 →L[ℂ] Lp ℂ 2 (cubicThetaPointMeasure.restrict K) :=
  (cubicThetaCompactBorelRestrictionLinear hK).mkContinuousOfExistsBound
    (cubicThetaCompactBorelRestrictionLinear_bound hK)

lemma cubicThetaCompactBorelRestriction_coe {K : Set CubicThetaPoint} (hK : IsCompact K) (F : CubicThetaGlobalL2) :
    cubicThetaCompactBorelRestriction hK F =ᵐ[cubicThetaPointMeasure.restrict K]
      cubicThetaBorelLift (F : CubicThetaQuotient → ℂ) :=
  (cubicThetaBorelLift_compact_memLp hK
    (Lp.stronglyMeasurable F).measurable (Lp.memLp F)).coeFn_toLp

lemma cubicThetaCompactBorelRestriction_section {K : Set CubicThetaPoint} (hK : IsCompact K)
    (F : CubicThetaSection) (hF : MemLp (cubicThetaSectionRepresentative F) 2 cubicThetaQuotientMeasure) :
    cubicThetaCompactBorelRestriction hK (hF.toLp _)=ᵐ[cubicThetaPointMeasure.restrict K] F.val := by
  filter_upwards [cubicThetaCompactBorelRestriction_coe hK (hF.toLp _),
    cubicThetaCompact_pull_ae hK hF.coeFn_toLp] with p hp hq
  rw [hp]
  change cubicThetaBorelPhase p*(hF.toLp _) (cubicThetaQuotientMap p)=_
  rw [hq]
  exact cubicThetaBorelLift_section F p

end CubicFirstMoment

end

end OAI
