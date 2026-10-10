import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.KernelBasic
import OAI.Analysis.RieszRectifiability.Kernel.EnergyFromTruncations

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function Filter Topology
open scoped ENNReal

def positiveNormalHeight {d : ℕ} (e x : Ambient d) : ℝ := max 0 (inner ℝ e x)

def positiveNormalPotential {d : ℕ} (n : ℕ) (e x : Ambient d) : ℝ :=
  positiveNormalHeight e x / ‖x‖ ^ (n + 1)

theorem positiveNormalHeight_nonneg {d : ℕ} (e x : Ambient d) :
    0 ≤ positiveNormalHeight e x := le_max_left _ _

theorem positiveNormalHeight_le_norm {d : ℕ} (e x : Ambient d) :
    positiveNormalHeight e x ≤ ‖e‖ * ‖x‖ := by
  exact max_le (by positivity) (real_inner_le_norm e x)

theorem positiveNormalPotential_nonneg {d : ℕ} (n : ℕ) (e x : Ambient d) :
    0 ≤ positiveNormalPotential n e x :=
  div_nonneg (positiveNormalHeight_nonneg e x) (by positivity)

theorem positiveNormalPotential_zero {d : ℕ} (n : ℕ) (e : Ambient d) :
    positiveNormalPotential n e 0 = 0 := by
  simp [positiveNormalPotential, positiveNormalHeight]

theorem positiveNormalPotential_measurable {d : ℕ} (n : ℕ) (e : Ambient d) :
    Measurable (positiveNormalPotential n e) := by
  unfold positiveNormalPotential positiveNormalHeight
  fun_prop

theorem positiveNormalPotential_truncated_bound {d : ℕ} (n : ℕ) (e x : Ambient d)
    (ε R : ℝ) (hε : 0 < ε) (hsmall : ε ≤ ‖x‖) (hlarge : ‖x‖ ≤ R) :
    positiveNormalPotential n e x ≤ (‖e‖ * R) * (ε ^ (n + 1))⁻¹ := by
  have hnum : positiveNormalHeight e x ≤ ‖e‖ * R :=
    (positiveNormalHeight_le_norm e x).trans (mul_le_mul_of_nonneg_left hlarge (norm_nonneg e))
  have hinv : (‖x‖ ^ (n + 1))⁻¹ ≤ (ε ^ (n + 1))⁻¹ := by
    simpa only [one_div] using! one_div_le_one_div_of_le (pow_pos hε (n + 1))
      (pow_le_pow_left₀ hε.le hsmall (n + 1))
  exact mul_le_mul hnum hinv (by positivity)
    (mul_nonneg (norm_nonneg e) ((norm_nonneg x).trans hlarge))

theorem positiveNormalPotential_integrableOn_truncated {d : ℕ} (n : ℕ)
    (μ : Measure (Ambient d)) [IsFiniteMeasureOnCompacts μ] (e : Ambient d)
    (ε R : ℝ) (hε : 0 < ε) :
    IntegrableOn (positiveNormalPotential n e)
      (ball (0 : Ambient d) R ∩ {x | ε < ‖x‖}) μ := by
  apply Measure.integrableOn_of_bounded
    ((measure_mono (inter_subset_left.trans ball_subset_closedBall)).trans_lt
      (isCompact_closedBall (0 : Ambient d) R).measure_lt_top).ne
    (positiveNormalPotential_measurable n e).aestronglyMeasurable
  filter_upwards [ae_restrict_mem
    (measurableSet_ball.inter (measurableSet_lt measurable_const continuous_norm.measurable))] with x hx
  rw [Real.norm_of_nonneg (positiveNormalPotential_nonneg n e x)]
  exact positiveNormalPotential_truncated_bound n e x ε R hε hx.2.le
    (mem_ball_zero_iff.mp hx.1).le

theorem positiveNormalPotential_integrable_of_truncated_bounds {d : ℕ} (n : ℕ)
    (μ : Measure (Ambient d)) [IsFiniteMeasureOnCompacts μ]
    (e : Ambient d) (R B : ℝ)
    (hB : ∀ ε : ℝ, 0 < ε →
      (∫ x in ball (0 : Ambient d) R ∩ {x | ε < ‖x‖}, positiveNormalPotential n e x ∂μ) ≤ B) :
    IntegrableOn (positiveNormalPotential n e) (ball (0 : Ambient d) R) μ ∧
      (∫ x in ball (0 : Ambient d) R, positiveNormalPotential n e x ∂μ) ≤ B := by
  apply nonnegative_integrable_of_exhaustion (μ.restrict (ball (0 : Ambient d) R))
    (positiveNormalPotential n e) (positiveNormalPotential_measurable n e)
    (positiveNormalPotential_nonneg n e)
    (fun k : ℕ => {x : Ambient d | (1 / 2 : ℝ) ^ k < ‖x‖})
    (fun _ => measurableSet_lt measurable_const continuous_norm.measurable)
  · intro k l hkl x hx
    have hp : (1 / 2 : ℝ) ^ l ≤ (1 / 2 : ℝ) ^ k :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hkl
    exact lt_of_le_of_lt hp hx
  · intro x hx
    have hne : x ≠ 0 := by
      intro h
      exact hx (h ▸ positiveNormalPotential_zero n e)
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (norm_pos_iff.mpr hne)
      (by norm_num : (1 / 2 : ℝ) < 1)
    exact mem_iUnion.mpr ⟨k, hk⟩
  · intro k
    simpa only [IntegrableOn, Measure.restrict_restrict
      (measurableSet_lt measurable_const continuous_norm.measurable), inter_comm] using!
      positiveNormalPotential_integrableOn_truncated n μ e ((1 / 2 : ℝ) ^ k) R (by positivity)
  · intro k
    simpa only [Measure.restrict_restrict
      (measurableSet_lt measurable_const continuous_norm.measurable), inter_comm] using!
      hB ((1 / 2 : ℝ) ^ k) (by positivity)

end

end RieszRectifiability

end OAI
