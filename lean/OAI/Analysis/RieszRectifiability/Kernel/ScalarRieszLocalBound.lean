import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.ScalarRieszTestBounds

namespace OAI

/-!
# Uniform local bounds for scalar Riesz transforms

Near and far inverse-distance kernels give an integrable majorant for symmetric
Schwartz test kernels. Its coefficients depend on Schwartz seminorms and a bound
on the base point, yielding a local bound uniform over positive truncation scales.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory SchwartzMap Metric Filter Topology Set

def scalarRieszLocalDominator {d : ℕ} (p : ℕ) (e : Ambient d)
    (g : 𝓢(Ambient d, ℝ)) (R : ℝ) (h : Ambient d) : ℝ :=
  (2 * ‖e‖ * SchwartzMap.seminorm ℝ 0 0 (fderivCLM ℝ (Ambient d) ℝ g)) *
    (closedBall (0 : Ambient d) 1).indicator (inverseDistancePow p 0) h +
  (4 * ‖e‖ * (SchwartzMap.seminorm ℝ 1 0 g + R * SchwartzMap.seminorm ℝ 0 0 g)) *
    (closedExterior (0 : Ambient d) 1).indicator (inverseDistancePow (p + 2) 0) h

theorem scalarRieszLocalDominator_integrable (p : ℕ) (e : Ambient (p + 1))
    (g : 𝓢(Ambient (p + 1), ℝ)) (R : ℝ) :
    Integrable (scalarRieszLocalDominator p e g R) volume := by
  have hn := (inverseDistancePow_near_integrable_and_bound (d := p + 1) p _ volume
    (volume_global_upper_growth (p + 1)) 0 1 (by norm_num)).1
  have hf := (inverseDistancePow_closedExterior_integrable_and_bound (d := p + 1) (p + 1) _ volume
    (volume_global_upper_growth (p + 1)) 0 1 (by norm_num)).1
  exact ((hn.integrable_indicator measurableSet_closedBall).const_mul _).add
    ((hf.integrable_indicator (closedExterior_measurable 0 1)).const_mul _)

theorem symmetricScalarRieszTestKernel_le_localDominator {d : ℕ} (p : ℕ)
    (e : Ambient d) (g : 𝓢(Ambient d, ℝ)) (R : ℝ) (x h : Ambient d) (hx : ‖x‖ ≤ R) :
    ‖symmetricScalarRieszTestKernel (p + 1) e g x h‖ ≤ scalarRieszLocalDominator p e g R h := by
  have hR : 0 ≤ R := (norm_nonneg _).trans hx
  have hn : 0 ≤ (closedBall (0 : Ambient d) 1).indicator (inverseDistancePow p 0) h :=
    indicator_nonneg (fun y _ => inverseDistancePow_nonneg p 0 y) h
  have hf : 0 ≤ (closedExterior (0 : Ambient d) 1).indicator (inverseDistancePow (p + 2) 0) h :=
    indicator_nonneg (fun y _ => inverseDistancePow_nonneg (p + 2) 0 y) h
  have hnear : 0 ≤ (2 * ‖e‖ * SchwartzMap.seminorm ℝ 0 0 (fderivCLM ℝ (Ambient d) ℝ g)) *
      (closedBall (0 : Ambient d) 1).indicator (inverseDistancePow p 0) h :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (norm_nonneg _)) (apply_nonneg _ _)) hn
  by_cases hh : ‖h‖ ≤ 1
  · have hmem : h ∈ closedBall (0 : Ambient d) 1 := by
      simpa only [mem_closedBall, dist_zero_right] using! hh
    unfold scalarRieszLocalDominator
    rw [indicator_of_mem hmem]
    apply (symmetricScalarRieszTestKernel_near_bound p e g x h).trans
    apply le_add_of_nonneg_right
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (norm_nonneg _))
      (add_nonneg (apply_nonneg _ _) (mul_nonneg hR (apply_nonneg _ _)))) hf
  · have hmem : h ∈ closedExterior (0 : Ambient d) 1 := by
      simpa only [closedExterior, mem_ofPred_eq, dist_zero_left] using! (lt_of_not_ge hh).le
    unfold scalarRieszLocalDominator
    rw [indicator_of_mem hmem]
    apply (symmetricScalarRieszTestKernel_far_bound (p + 1) e g x h).trans
    apply le_trans _ (le_add_of_nonneg_left hnear)
    apply mul_le_mul_of_nonneg_right _ (inverseDistancePow_nonneg _ _ _)
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num) (norm_nonneg _))
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hx
      (show 0 ≤ SchwartzMap.seminorm ℝ 0 0 g from apply_nonneg _ _))

theorem exists_uniform_local_scalarCappedTransform_bound (p : ℕ) (e : Ambient (p + 1))
    (g : 𝓢(Ambient (p + 1), ℝ)) (R : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ ε : ℝ, 0 < ε → ∀ x : Ambient (p + 1), ‖x‖ ≤ R →
      |scalarCappedTransform (p + 1) volume e ε g x| ≤ B := by
  let D := scalarRieszLocalDominator p e g R
  let B := ∫ h, ‖D h‖
  have hD : Integrable D volume := scalarRieszLocalDominator_integrable p e g R
  have hB : 0 ≤ B := integral_nonneg fun _ => norm_nonneg _
  refine ⟨B, hB, ?_⟩
  intro ε hε x hx
  obtain ⟨hI, heq⟩ := scalarCappedTransform_symmetric_identity (p + 1) e ε hε g
    g.continuous.measurable g.integrable x
  have hb : |∫ h, symmetricScalarCappedTestKernel (p + 1) e ε g x h| ≤ B := by
    calc
      _ ≤ ∫ h, ‖symmetricScalarCappedTestKernel (p + 1) e ε g x h‖ := by
        simpa only [Real.norm_eq_abs] using! norm_integral_le_integral_norm
          (μ := volume) (symmetricScalarCappedTestKernel (p + 1) e ε g x)
      _ ≤ B := by
        apply integral_mono hI.norm hD.norm
        intro h
        exact (symmetricScalarCappedTestKernel_norm_le (p + 1) e ε g x h).trans
          ((symmetricScalarRieszTestKernel_le_localDominator p e g R x h hx).trans (le_abs_self _))
  rw [heq, abs_mul]
  norm_num
  nlinarith

end

end RieszRectifiability

end OAI
