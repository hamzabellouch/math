import Mathlib
import OAI.Probability.SKBarriers.Hierarchy.CascadeRecursion
import OAI.Probability.SKBarriers.Scalar.ThermalMoments

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
section OneStep
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem gaussianStep_spin_curvature {f : E × ℝ → ℝ} (hf : BoundedDerivs f)
    {m : ℝ} (hm : m ∈ Set.Icc 0 1) (u x : E)
    (hH : ∀ y, 0 < prefixHessian f u u (x,y) ∧
      prefixHessian f u u (x,y) ≤ 1-(prefixGradient f u (x,y))^2) :
    0 < fderiv ℝ (fderiv ℝ (gaussianStep m f)) x u u ∧
      fderiv ℝ (fderiv ℝ (gaussianStep m f)) x u u ≤
        1-(fderiv ℝ (gaussianStep m f) x u)^2 := by
  let μ := gaussianStepLaw m f x
  let := gaussianStepLaw_probability hf m x
  obtain ⟨hcG,B,_hB,hbG⟩ := prefixGradient_data hf u
  obtain ⟨hcH,C,_hC,hbH⟩ := prefixHessian_data hf u u
  have hcm : Continuous (fun y : ℝ => prefixGradient f u (x,y)) := hcG.comp (continuous_const.prodMk (continuous_id : Continuous (fun y : ℝ => y)))
  have hmem : MemLp (fun y => prefixGradient f u (x,y)) 2 μ :=
    MemLp.of_bound hcm.aestronglyMeasurable B (ae_of_all _ (fun y => hbG (x,y)))
  have iH : Integrable (fun y => prefixHessian f u u (x,y)) μ :=
    integrable_gaussianStep_of_bounded hf m x
      (hcH.comp (continuous_const.prodMk continuous_id)) (fun y => hbH (x,y))
  have hv := variance_nonneg (fun y => prefixGradient f u (x,y)) μ
  rw [variance_eq_sub hmem] at hv
  have hpos : 0 < ∫ y, prefixHessian f u u (x,y) ∂μ := by
    rw [integral_pos_iff_support_of_nonneg (fun y => (hH y).1.le) iH]
    have he : Function.support (fun y => prefixHessian f u u (x,y)) = Set.univ := by
      ext y
      simp only [Function.mem_support,Set.mem_univ]
      exact iff_true_intro (hH y).1.ne'
    rw [he,measure_univ]
    exact zero_lt_one
  have hupper := integral_mono iH ((integrable_const (1:ℝ)).sub hmem.integrable_sq)
    (fun y => (hH y).2)
  change (∫ y, prefixHessian f u u (x,y) ∂μ) ≤
    ∫ y, 1-(prefixGradient f u (x,y))^2 ∂μ at hupper
  rw [integral_sub (integrable_const _) hmem.integrable_sq,integral_const] at hupper
  simp only [Measure.real,measure_univ,ENNReal.toReal_one,smul_eq_mul,one_mul] at hupper
  rw [fderiv_fderiv_gaussianStep_apply hf,fderiv_gaussianStep_apply hf]
  simp only [gaussianAverage,pow_two,Pi.mul_apply] at hv hupper ⊢
  dsimp only [μ] at hv hupper hpos
  constructor
  · nlinarith [mul_nonneg hm.1 hv]
  · nlinarith [mul_nonneg (sub_nonneg.mpr hm.2) hv]

theorem affineLogPartition_bool_curvature (L : E →L[ℝ] ℝ) (z u : E) (hL : L u = 1) :
    let f := affineLogPartition (fun _ : Bool => 0) (fun b => spin b • L)
    0 < fderiv ℝ (fderiv ℝ f) z u u ∧
      fderiv ℝ (fderiv ℝ f) z u u = 1-(fderiv ℝ f z u)^2 := by
  dsimp only
  rw [fderiv_fderiv_affineLogPartition_apply,fderiv_affineLogPartition_apply]
  have hpos₀ := affineGibbs_pos (fun _ : Bool => 0) (fun b => spin b • L) z false
  have hpos₁ := affineGibbs_pos (fun _ : Bool => 0) (fun b => spin b • L) z true
  have hsum := affineGibbs_sum (fun _ : Bool => 0) (fun b => spin b • L) z
  simp only [Fintype.sum_bool] at hsum
  simp only [spin] at hpos₀ hpos₁ hsum
  simp only [affineMoment,Fintype.sum_bool,smul_apply,smul_eq_mul,hL,mul_one,
    spin,Bool.false_eq_true,ite_false,ite_true,neg_one_mul]
  constructor <;> nlinarith [mul_pos hpos₀ hpos₁]
end OneStep
attribute [local instance 1900] cascadeNormedGroup cascadeNormedSpace
section Cascade
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem cascade_spin_curvature (n : ℕ) (m : Fin n → ℝ)
    (f : CascadeSpace E n → ℝ) (hf : BoundedDerivs f)
    (hm : ∀ i, m i ∈ Set.Icc 0 1) (u : E)
    (hH : ∀ z, 0 < fderiv ℝ (fderiv ℝ f) z (cascadeLift n u) (cascadeLift n u) ∧
      fderiv ℝ (fderiv ℝ f) z (cascadeLift n u) (cascadeLift n u) ≤
        1-(fderiv ℝ f z (cascadeLift n u))^2) (x : E) :
    0 < fderiv ℝ (fderiv ℝ (cascadePressure n m f)) x u u ∧
      fderiv ℝ (fderiv ℝ (cascadePressure n m f)) x u u ≤
        1-(fderiv ℝ (cascadePressure n m f) x u)^2 := by
  induction n with
  | zero => exact hH x
  | succ n ih =>
    apply ih (fun i => m i.castSucc) _ (hf.gaussianStep _) (fun i => hm i.castSucc)
    intro z
    apply gaussianStep_spin_curvature hf (hm (Fin.last n)) (cascadeLift n u) z
    intro y
    exact hH (z,y)
end Cascade
end SK.Analytic

end
end

end

end OAI
