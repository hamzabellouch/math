import Mathlib
import OAI.Probability.LogConcave.Sampling.JointInterpolationLaw

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology

namespace LogConcaveSampling
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

lemma integrable_lipschitz_comp_of_integrable {Ω E G : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] [NormedAddCommGroup E] [NormedAddCommGroup G]
    {X : Ω → E} (hX : Integrable X μ) {g : E → G} {L : ℝ≥0} (hg : LipschitzWith L g) :
    Integrable (fun ω => g (X ω)) μ := by
  apply ((integrable_const ‖g 0‖).add (hX.norm.const_mul (L:ℝ))).mono'
    (hg.continuous.comp_aestronglyMeasurable hX.aestronglyMeasurable)
  filter_upwards [] with ω
  have hh := hg.dist_le_mul (X ω) 0
  rw [dist_eq_norm,dist_zero_right] at hh
  calc
    ‖g (X ω)‖ ≤ ‖g 0‖+‖g (X ω)-g 0‖ := norm_le_norm_add_norm_sub' _ _
    _ ≤ ‖g 0‖+(L:ℝ)*‖X ω‖ := by linarith

lemma primitive_identity_integrable {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r : ℝ} (hr : 0≤r) (hl : (lam:ℝ)*r^2<1) :
    Integrable (fun z => z) (gibbs (primitivePotential F x r)) := by
  let := probability_gibbs_of_partition
    (partition_pos_of_continuous (hF.continuous_potential x r)).ne'
    (partition_ne_top_of_integrable (hF.integrable_exp_neg_potential x hr hl))
  exact (Appell.HasGrowth.lipschitz (LipschitzWith.id (α:=Point d))).integrable
    continuous_id.aestronglyMeasurable (hF.hasExpMoments x hr hl).hasMoments

def interpolationResidual {d : ℕ} (F : Point d → ℝ) (x : Point d) (r ρ : ℝ)
    (p : Point d × Point d) : Point d :=
  (1/(1-ρ^2)) • (p.1-ρ • p.2)+r • conditionalFieldMean F x r ρ p.2

lemma interpolationResidual_integrable {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1) :
    Integrable (interpolationResidual F x r ρ) (jointInterpolationLaw F x r ρ) := by
  let μ := gibbs (primitivePotential F x r)
  let ν := stdGaussian (Point d)
  let := probability_gibbs_of_partition
    (partition_pos_of_continuous (hF.continuous_potential x r)).ne'
    (partition_ne_top_of_integrable (hF.integrable_exp_neg_potential x hr (by linarith)))
  have hi := primitive_identity_integrable hF x hr (by linarith : (lam:ℝ)*r^2<1)
  have hz : Integrable (fun p : Point d × Point d => p.1) (μ.prod ν) := hi.comp_fst ν
  have hg : Integrable (fun p : Point d × Point d => p.2) (μ.prod ν) :=
    (IsGaussian.integrable_id (μ:=ν)).comp_snd μ
  have hy := (hz.smul ρ).add (hg.smul (Real.sqrt (1-ρ^2)))
  have hM := conditionalFieldMean_lipschitz hF x hr hl hρ0 hρ1
  have hm := integrable_lipschitz_comp_of_integrable hy hM
  have hu := ((hz.sub (hy.smul ρ)).smul (1/(1-ρ^2))).add (hm.smul r)
  have hc : Continuous (interpolationResidual F x r ρ) := by
    unfold interpolationResidual
    exact ((continuous_fst.sub (continuous_snd.const_smul ρ)).const_smul (1/(1-ρ^2))).add
      ((hM.continuous.comp continuous_snd).const_smul r)
  apply (integrable_map_measure hc.aestronglyMeasurable (by fun_prop)).2
  exact hu

lemma conditional_residual_zero {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1) (y : Point d) :
    (∫ z,interpolationResidual F x r ρ (z,y) ∂gibbs (conditionalPotential F x r ρ y))=0 := by
  let := conditionalLaw_probability hF x hr hl hρ0 hρ1 y
  have hi := conditional_identity_integrable hF x hr hl hρ0 hρ1 y
  have hh := integral_scaled_affine_add hi (integrable_const
    (conditionalFieldMean F x r ρ y)) (1/(1-ρ^2)) r (ρ • y)
  rw [show (∫ z,interpolationResidual F x r ρ (z,y) ∂gibbs (conditionalPotential F x r ρ y))=
      (1/(1-ρ^2)) • ((∫ z,z ∂gibbs (conditionalPotential F x r ρ y))-ρ • y)+
        r • (∫ _,conditionalFieldMean F x r ρ y ∂gibbs (conditionalPotential F x r ρ y)) from hh,
    integral_const,probReal_univ,one_smul,conditional_mean_identity hF x hr hl hρ0 hρ1]
  have ha := (probability_time hρ0 hρ1).1
  rw [sub_sub_cancel_left,smul_neg,smul_smul]
  have he : 1/(1-ρ^2)*((1-ρ^2)*r)=r := by field_simp
  rw [he,neg_add_cancel]

lemma integrable_scaled_affine_const {d : ℕ} {μ : Measure (Point d)} [IsFiniteMeasure μ]
    (hi : Integrable (fun z => z) μ) (c : ℝ) (a b : Point d) :
    Integrable (fun z => c • (z-a)+b) μ :=
  ((hi.sub (integrable_const a)).smul c).add (integrable_const b)

lemma conditional_residual_integrable {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1) (y : Point d) :
    Integrable (fun z => interpolationResidual F x r ρ (z,y))
      (gibbs (conditionalPotential F x r ρ y)) := by
  let := conditionalLaw_probability hF x hr hl hρ0 hρ1 y
  exact integrable_scaled_affine_const (conditional_identity_integrable hF x hr hl hρ0 hρ1 y)
    (1/(1-ρ^2)) (ρ • y) (r • conditionalFieldMean F x r ρ y)

theorem interpolation_flux_zero {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1)
    {T : Point d → Point d →L[ℝ] ℝ} (hT : Measurable T)
    {C : ℝ} (hC : ∀ y,‖T y‖≤C) :
    (∫ p,T p.2 (interpolationResidual F x r ρ p) ∂jointInterpolationLaw F x r ρ)=0 := by
  have hi := interpolationResidual_integrable hF x hr hl hρ0 hρ1
  have hM := conditionalFieldMean_lipschitz hF x hr hl hρ0 hρ1
  have hc : Continuous (interpolationResidual F x r ρ) := by
    unfold interpolationResidual
    exact ((continuous_fst.sub (continuous_snd.const_smul ρ)).const_smul (1/(1-ρ^2))).add
      ((hM.continuous.comp continuous_snd).const_smul r)
  have hm : Measurable (fun p => T p.2 (interpolationResidual F x r ρ p)) :=
    (continuous_fst.clm_apply continuous_snd).measurable.comp
      ((hT.comp measurable_snd).prodMk hc.measurable)
  apply interpolation_joint_integral_zero hF x hr hl hρ0 hρ1
  · refine (hi.norm.const_mul C).mono' hm.aestronglyMeasurable (Filter.Eventually.of_forall fun p => ?_)
    exact ((T p.2).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hC p.2) (norm_nonneg _))
  · intro y
    have hrz := conditional_residual_integrable hF x hr hl hρ0 hρ1 y
    rw [(T y).integral_comp_comm hrz,conditional_residual_zero hF x hr hl hρ0 hρ1,map_zero]
end LogConcaveSampling

open Function MeasureTheory Set Filter
open scoped Topology NNReal

end UpperProof
end
end
end

end OAI
