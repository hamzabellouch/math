import Mathlib
import OAI.Probability.SKBarriers.Hierarchy.CascadeBlockLaw
import OAI.Probability.SKBarriers.Hierarchy.RootCalculus

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

def RootBoundedCurvature (n : ℕ) (f : ParameterSpace n → ℝ) : Prop :=
  ∀ z, 0 ≤ rootHessian n f z ∧ rootHessian n f z ≤ 1-(rootGradient n f z)^2

theorem RootBoundedCurvature.gaussianStep {n : ℕ} {f : ParameterSpace (n+1) → ℝ}
    (h : RootBoundedCurvature (n+1) f) (hf : BoundedDerivs f) {m : ℝ}
    (hm : m ∈ Icc (0:ℝ) 1) : RootBoundedCurvature n (Analytic.gaussianStep m f) := by
  intro x
  let μ := gaussianStepLaw m f x
  let := gaussianStepLaw_probability hf m x
  let u := parameterAxis n
  obtain ⟨hcG,B,_hB,hbG⟩ := prefixGradient_data hf u
  obtain ⟨hcH,C,_hC,hbH⟩ := prefixHessian_data hf u u
  have hmem : MemLp (fun y => prefixGradient f u (x,y)) 2 μ :=
    MemLp.of_bound (hcG.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
      B (ae_of_all _ (fun y => hbG (x,y)))
  have iH : Integrable (fun y => prefixHessian f u u (x,y)) μ :=
    integrable_gaussianStep_of_bounded hf m x
      (hcH.comp (continuous_const.prodMk continuous_id)) (fun y => hbH (x,y))
  have hv := variance_nonneg (fun y => prefixGradient f u (x,y)) μ
  rw [variance_eq_sub hmem] at hv
  have hpos : 0 ≤ ∫ y, prefixHessian f u u (x,y) ∂μ :=
    integral_nonneg (fun y => (h (x,y)).1)
  have hupper := integral_mono iH ((integrable_const (1:ℝ)).sub hmem.integrable_sq)
    (fun y => (h (x,y)).2)
  change (∫ y, prefixHessian f u u (x,y) ∂μ) ≤
    ∫ y, 1-(prefixGradient f u (x,y))^2 ∂μ at hupper
  rw [integral_sub (integrable_const _) hmem.integrable_sq,integral_const] at hupper
  simp only [Measure.real,measure_univ,ENNReal.toReal_one,smul_eq_mul,one_mul] at hupper
  change 0 ≤ fderiv ℝ (fderiv ℝ (Analytic.gaussianStep m f)) x u u ∧
    fderiv ℝ (fderiv ℝ (Analytic.gaussianStep m f)) x u u ≤ 1-(fderiv ℝ (Analytic.gaussianStep m f) x u)^2
  rw [fderiv_fderiv_gaussianStep_apply hf,fderiv_gaussianStep_apply hf]
  simp only [gaussianAverage,pow_two,Pi.mul_apply] at hv hupper ⊢
  dsimp only [μ] at hv hupper hpos
  constructor
  · nlinarith [mul_nonneg hm.1 hv]
  · nlinarith [mul_nonneg (sub_nonneg.mpr hm.2) hv]

theorem RootBoundedCurvature.hierarchyPressure {n : ℕ} {f : ParameterSpace n → ℝ}
    (h : RootBoundedCurvature n f) (hf : BoundedDerivs f) (m : Fin n → ℝ)
    (hm : ∀ i, m i ∈ Icc (0:ℝ) 1) : RootBoundedCurvature 0 (hierarchyPressure n m f) := by
  induction n with
  | zero => exact h
  | succ n ih =>
    exact ih (h.gaussianStep hf (hm (Fin.last n))) (hf.gaussianStep _) _ (fun j => hm j.castSucc)

theorem affineLogPartition_bounded_root {S : Type} [Fintype S] [Nonempty S]
    (n : ℕ) (c : S → ℝ) (U : S → ParameterSpace n →L[ℝ] ℝ)
    (hU : ∀ s, |U s (parameterAxis n)| ≤ 1) :
    RootBoundedCurvature n (affineLogPartition c U) := by
  intro z
  simp only [rootHessian,rootGradient,fderiv_fderiv_affineLogPartition_apply,
    fderiv_affineLogPartition_apply]
  have hv := affineMoment_variance_nonneg c U (fun s => U s (parameterAxis n)) z
  have hupper := affineMoment_norm_le c U (fun s => (U s (parameterAxis n))^2)
    (C:=1) (fun s => by
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      exact (sq_le_one_iff_abs_le_one _).mpr (hU s)) z
  simp only [pow_two] at hv hupper
  constructor
  · exact hv
  · have hh := le_trans (le_abs_self _) hupper
    nlinarith

theorem hierarchy_bounded_observable_curvature {S : Type} [Fintype S] [Nonempty S]
    (n : ℕ) (m : Fin n → ℝ) (hm : ∀ i, m i ∈ Icc (0:ℝ) 1)
    (c : S → ℝ) (U : S → ParameterSpace n →L[ℝ] ℝ)
    (hU : ∀ s, |U s (parameterAxis n)| ≤ 1) :
    RootBoundedCurvature 0 (hierarchyPressure n m (affineLogPartition c U)) :=
  (affineLogPartition_bounded_root n c U hU).hierarchyPressure
    (affineLogPartition_boundedDerivs c U) m hm

end SK.Analytic

end
end

end OAI
