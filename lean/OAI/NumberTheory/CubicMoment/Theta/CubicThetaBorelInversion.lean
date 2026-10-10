import OAI.NumberTheory.CubicMoment.Theta.CubicThetaBorelPullback
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaInversionMass

namespace OAI

/-! The actual inversion operator on quotient representatives, including
the cubic phase of the chosen Borel section. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

def cubicThetaBorelInversionFunction (f : CubicThetaQuotient → ℂ)
    (q : CubicThetaQuotient) : ℂ :=
  cubicThetaBorelLift f (cubicThetaFullInversion • cubicThetaBorelSection q)

lemma cubicThetaBorelInversionFunction_measurable {f : CubicThetaQuotient → ℂ}
    (hf : Measurable f) : Measurable (cubicThetaBorelInversionFunction f) :=
  (cubicThetaBorelLift_measurable hf).comp
    ((measurable_const_smul cubicThetaFullInversion).comp cubicThetaBorelSection_measurable)

lemma cubicThetaBorelInversionFunction_norm (f : CubicThetaQuotient → ℂ)
    (q : CubicThetaQuotient) :
    ‖cubicThetaBorelInversionFunction f q‖=
      ‖f (cubicThetaIntegralQuotientMap cubicThetaFullInversion q)‖ := by
  rw [cubicThetaBorelInversionFunction,cubicThetaBorelLift_norm,
    ←cubicThetaIntegralQuotientMap_apply,cubicThetaBorelSection_rightInverse q]

lemma cubicThetaBorelInversionFunction_lift (f : CubicThetaQuotient → ℂ)
    (p : CubicThetaPoint) :
    cubicThetaBorelLift (cubicThetaBorelInversionFunction f) p=
      cubicThetaBorelLift f (cubicThetaFullInversion • p) := by
  obtain ⟨g,hg⟩ := cubicThetaBorelSheet_cover p
  rw [cubicThetaBorelLift,cubicThetaBorelPhase_sheet g hg,cubicThetaBorelInversionFunction,
    ←cubicThetaInversionConjugate_character g,←cubicThetaBorelLift_automorphy,
    ←cubicThetaInversion_intertwine]
  exact congrArg (fun x => cubicThetaBorelLift f (cubicThetaFullInversion • x)) hg

lemma cubicThetaBorelInversionFunction_memLp (f : CubicThetaGlobalL2) :
    MemLp (cubicThetaBorelInversionFunction f) 2 cubicThetaQuotientMeasure := by
  have hf := (Lp.memLp f).comp_measurePreserving
    (cubicThetaIntegralQuotient_measurePreserving cubicThetaFullInversion)
  apply (memLp_norm_iff (cubicThetaBorelInversionFunction_measurable
    (Lp.stronglyMeasurable f).measurable).aestronglyMeasurable).mp
  simpa only [cubicThetaBorelInversionFunction_norm,Function.comp_def] using hf.norm

def cubicThetaBorelInversionLinear : CubicThetaGlobalL2 →ₗ[ℂ] CubicThetaGlobalL2 where
  toFun f := (cubicThetaBorelInversionFunction_memLp f).toLp _
  map_add' f g := by
    apply Lp.ext
    have hsum := (cubicThetaIntegralQuotient_measurePreserving
      cubicThetaFullInversion).quasiMeasurePreserving.ae (Lp.coeFn_add f g)
    filter_upwards [(cubicThetaBorelInversionFunction_memLp (f+g)).coeFn_toLp,
      (cubicThetaBorelInversionFunction_memLp f).coeFn_toLp,
      (cubicThetaBorelInversionFunction_memLp g).coeFn_toLp,
      Lp.coeFn_add ((cubicThetaBorelInversionFunction_memLp f).toLp _)
        ((cubicThetaBorelInversionFunction_memLp g).toLp _),hsum] with q hfg hf hg hadd hq
    change ((cubicThetaBorelInversionFunction_memLp (f+g)).toLp _) q=_
    rw [hfg,hadd]
    simp only [Pi.add_apply]
    rw [hf,hg]
    simp only [Pi.add_apply] at hq
    simp only [cubicThetaBorelInversionFunction,cubicThetaBorelLift,
      ←cubicThetaIntegralQuotientMap_apply,cubicThetaBorelSection_rightInverse q]
    rw [hq,mul_add]
  map_smul' c f := by
    apply Lp.ext
    have hsum := (cubicThetaIntegralQuotient_measurePreserving
      cubicThetaFullInversion).quasiMeasurePreserving.ae (Lp.coeFn_smul c f)
    filter_upwards [(cubicThetaBorelInversionFunction_memLp (c • f)).coeFn_toLp,
      (cubicThetaBorelInversionFunction_memLp f).coeFn_toLp,
      Lp.coeFn_smul c ((cubicThetaBorelInversionFunction_memLp f).toLp _),hsum]
      with q hcf hf hsm hq
    change ((cubicThetaBorelInversionFunction_memLp (c • f)).toLp _) q=_
    simp only [RingHom.id_apply]
    rw [hcf,hsm]
    simp only [Pi.smul_apply]
    rw [hf]
    simp only [Pi.smul_apply,smul_eq_mul] at hq ⊢
    simp only [cubicThetaBorelInversionFunction,cubicThetaBorelLift,
      ←cubicThetaIntegralQuotientMap_apply,cubicThetaBorelSection_rightInverse q]
    rw [hq]
    ring

lemma cubicThetaBorelInversionLinear_norm (f : CubicThetaGlobalL2) :
    ‖cubicThetaBorelInversionLinear f‖=‖f‖ := by
  apply (sq_eq_sq₀ (_root_.norm_nonneg _) (_root_.norm_nonneg _)).mp
  rw [cubicTheta_l2_norm_sq_measure,cubicTheta_l2_norm_sq_measure]
  calc
    _ = ∫ q,‖f (cubicThetaIntegralQuotientMap cubicThetaFullInversion q)‖^2
        ∂cubicThetaQuotientMeasure := by
      apply integral_congr_ae
      filter_upwards [(cubicThetaBorelInversionFunction_memLp f).coeFn_toLp] with q hq
      change ‖((cubicThetaBorelInversionFunction_memLp f).toLp _) q‖^2=_
      rw [hq,cubicThetaBorelInversionFunction_norm]
    _ = _ := (cubicThetaIntegralQuotient_measurePreserving cubicThetaFullInversion).integral_comp
      (cubicThetaIntegralQuotientHomeomorph cubicThetaFullInversion).measurableEmbedding
      (fun q => ‖f q‖^2)

def cubicThetaBorelInversion : CubicThetaGlobalL2 →ₗᵢ[ℂ] CubicThetaGlobalL2 :=
  ⟨cubicThetaBorelInversionLinear,cubicThetaBorelInversionLinear_norm⟩

theorem cubicThetaBorelInversion_lift (f : CubicThetaGlobalL2) :
    cubicThetaBorelLift (cubicThetaBorelInversion f)
      =ᵐ[cubicThetaPointMeasure] fun p => cubicThetaBorelLift f (cubicThetaFullInversion • p) := by
  filter_upwards [cubicThetaQuotient_pull_ae
    (cubicThetaBorelInversionFunction_memLp f).coeFn_toLp] with p hp
  change ((cubicThetaBorelInversionFunction_memLp f).toLp _)
    (cubicThetaQuotientMap p)=_ at hp
  change cubicThetaBorelPhase p*((cubicThetaBorelInversionFunction_memLp f).toLp _)
    (cubicThetaQuotientMap p)=_
  rw [hp]
  exact cubicThetaBorelInversionFunction_lift f p

end CubicFirstMoment

end

end OAI
