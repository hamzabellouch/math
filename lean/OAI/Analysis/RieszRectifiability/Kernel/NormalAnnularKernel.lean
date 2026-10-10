import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.PositiveNormalPotential

namespace OAI

/-!
# Normal components of annular kernel integrals

Away from the origin the Riesz kernel is integrable on bounded annuli. For measures
supported in a nonnegative half-space, its normal component equals the positive
normal potential, so vector integral bounds control the scalar potential integral.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology

theorem rieszKernel_integrableOn_centered_annulus {d : ℕ} (n : ℕ)
    (μ : Measure (Ambient d)) [IsFiniteMeasureOnCompacts μ] (ε R : ℝ) (hε : 0 < ε) :
    IntegrableOn (fun x : Ambient d => kernel n x 0)
      (ball (0 : Ambient d) R ∩ {x | ε < ‖x‖}) μ := by
  have : IsBoundedSMul ℝ (Ambient d) := NormedSpace.toIsBoundedSMul
  have : ContinuousSMul ℝ (Ambient d) := IsBoundedSMul.continuousSMul
  have : MeasurableSMul₂ ℝ (Ambient d) := ContinuousSMul.measurableSMul₂
  apply Measure.integrableOn_of_bounded
    ((measure_mono (inter_subset_left.trans ball_subset_closedBall)).trans_lt
      (isCompact_closedBall (0 : Ambient d) R).measure_lt_top).ne
    (show Measurable (fun x : Ambient d => kernel n x 0) by unfold kernel; fun_prop).aestronglyMeasurable
  filter_upwards [ae_restrict_mem
    (measurableSet_ball.inter (measurableSet_lt measurable_const continuous_norm.measurable))] with x hx
  exact kernel_norm_le_truncation n x 0 ε hε (by simpa only [dist_zero_right] using! hx.2.le)

theorem positiveNormalPotential_eq_kernel_component {d : ℕ} (n : ℕ) (e x : Ambient d)
    (hside : 0 ≤ inner ℝ e x) :
    positiveNormalPotential n e x = inner ℝ e (kernel n x 0) := by
  rw [positiveNormalPotential, positiveNormalHeight, max_eq_right hside,
    kernel, sub_zero, inner_smul_right]
  ring

theorem positiveNormalPotential_annulus_integral_eq {d : ℕ} (n : ℕ)
    (μ : Measure (Ambient d)) [IsFiniteMeasureOnCompacts μ]
    (e : Ambient d) (hside : ∀ x ∈ μ.support, 0 ≤ inner ℝ e x)
    (ε R : ℝ) (hε : 0 < ε) :
    (∫ x in ball (0 : Ambient d) R ∩ {x | ε < ‖x‖}, positiveNormalPotential n e x ∂μ) =
      inner ℝ e (∫ x in ball (0 : Ambient d) R ∩ {x | ε < ‖x‖}, kernel n x 0 ∂μ) := by
  calc
    _ = ∫ x in ball (0 : Ambient d) R ∩ {x | ε < ‖x‖}, inner ℝ e (kernel n x 0) ∂μ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae μ.support_mem_ae] with x hx
      exact positiveNormalPotential_eq_kernel_component n e x (hside x hx)
    _ = _ := (innerSL ℝ e).integral_comp_comm (rieszKernel_integrableOn_centered_annulus n μ ε R hε)

theorem positiveNormalPotential_bound_of_vector_annulus_bound {d : ℕ} (n : ℕ)
    (μ : Measure (Ambient d)) [IsFiniteMeasureOnCompacts μ]
    (e : Ambient d) (hside : ∀ x ∈ μ.support, 0 ≤ inner ℝ e x)
    (R B : ℝ) (hB : ∀ ε : ℝ, 0 < ε →
      ‖∫ x in ball (0 : Ambient d) R ∩ {x | ε < ‖x‖}, kernel n x 0 ∂μ‖ ≤ B) :
    ∀ ε : ℝ, 0 < ε →
      (∫ x in ball (0 : Ambient d) R ∩ {x | ε < ‖x‖}, positiveNormalPotential n e x ∂μ) ≤ ‖e‖ * B := by
  intro ε hε
  rw [positiveNormalPotential_annulus_integral_eq n μ e hside ε R hε]
  exact (real_inner_le_norm e _).trans (mul_le_mul_of_nonneg_left (hB ε hε) (norm_nonneg e))

end

end RieszRectifiability

end OAI
