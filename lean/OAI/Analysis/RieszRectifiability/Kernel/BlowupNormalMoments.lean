import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.BlowupMeasure
import OAI.Analysis.RieszRectifiability.Foundations.PositiveNormalPotential

namespace OAI

/-!
# Normal-height moments under blowup

Positive normal height is homogeneous of degree one. Combining this with the measure's
blowup normalization gives the moment scaling identity and bounds the rescaled height
integral by the positive normal potential on the original ball.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

theorem positiveNormalHeight_continuous {d : ℕ} (e : Ambient d) :
    Continuous (positiveNormalHeight e) := by
  unfold positiveNormalHeight
  fun_prop

theorem positiveNormalHeight_smul {d : ℕ} (e x : Ambient d) (r : ℝ) (hr : 0 ≤ r) :
    positiveNormalHeight e (r • x) = r * positiveNormalHeight e x := by
  simp only [positiveNormalHeight, inner_smul_right, mul_max_of_nonneg _ _ hr, mul_zero]

theorem positiveNormalHeight_integrableOn_ball {d : ℕ} (μ : Measure (Ambient d))
    [IsFiniteMeasureOnCompacts μ] (e : Ambient d) (R : ℝ) :
    IntegrableOn (positiveNormalHeight e) (ball (0 : Ambient d) R) μ :=
  ((positiveNormalHeight_continuous e).continuousOn.integrableOn_compact
    (isCompact_closedBall (0 : Ambient d) R)).mono_set ball_subset_closedBall

theorem blowup_positiveNormalHeight_integral {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (e : Ambient d) (r R : ℝ) (hr : 0 < r) :
    (∫ x in ball (0 : Ambient d) R, positiveNormalHeight e x ∂blowupMeasure n μ 0 r) =
      (r ^ (n + 1))⁻¹ * ∫ y in ball (0 : Ambient d) (r * R), positiveNormalHeight e y ∂μ := by
  let : ContinuousSMul ℝ (Ambient d) := IsBoundedSMul.continuousSMul
  rw [blowupMeasure, Measure.restrict_smul, integral_smul_measure,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ (r ^ n)⁻¹), smul_eq_mul,
    setIntegral_map measurableSet_ball (positiveNormalHeight_continuous e).aestronglyMeasurable
      (by fun_prop), blowup_preimage_ball 0 0 r R hr]
  simp only [smul_zero, add_zero, sub_zero]
  simp_rw [positiveNormalHeight_smul e _ r⁻¹ (inv_nonneg.mpr hr.le)]
  rw [integral_const_mul, pow_succ, mul_inv]
  ring

theorem positiveNormalHeight_eq_potential_weight {d : ℕ} (n : ℕ) (e x : Ambient d) :
    positiveNormalHeight e x = ‖x‖ ^ (n + 1) * positiveNormalPotential n e x := by
  by_cases hx : x = 0
  · subst x
    simp [positiveNormalHeight, positiveNormalPotential]
  · have hn : ‖x‖ ^ (n + 1) ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hx)
    unfold positiveNormalPotential
    field_simp

theorem blowup_positiveNormalHeight_le_potential_integral {d : ℕ} (n : ℕ)
    (μ : Measure (Ambient d)) [IsFiniteMeasureOnCompacts μ] (e : Ambient d)
    (r R : ℝ) (hr : 0 < r) (hR : 0 < R)
    (hi : IntegrableOn (positiveNormalPotential n e) (ball (0 : Ambient d) (r * R)) μ) :
    (∫ x in ball (0 : Ambient d) R, positiveNormalHeight e x ∂blowupMeasure n μ 0 r) ≤
      R ^ (n + 1) * ∫ y in ball (0 : Ambient d) (r * R), positiveNormalPotential n e y ∂μ := by
  have hbound : (∫ y in ball (0 : Ambient d) (r * R), positiveNormalHeight e y ∂μ) ≤
      (r * R) ^ (n + 1) * ∫ y in ball (0 : Ambient d) (r * R), positiveNormalPotential n e y ∂μ := by
    rw [← integral_const_mul]
    apply integral_mono_ae (positiveNormalHeight_integrableOn_ball μ e (r * R))
      (hi.const_mul ((r * R) ^ (n + 1)))
    filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
    rw [positiveNormalHeight_eq_potential_weight n e y]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (norm_nonneg y) (mem_ball_zero_iff.mp hy).le (n + 1))
      (positiveNormalPotential_nonneg n e y)
  rw [blowup_positiveNormalHeight_integral n μ e r R hr]
  calc
    _ ≤ (r ^ (n + 1))⁻¹ * ((r * R) ^ (n + 1) *
        ∫ y in ball (0 : Ambient d) (r * R), positiveNormalPotential n e y ∂μ) :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = _ := by
      rw [mul_pow]
      field_simp

end

end RieszRectifiability

end OAI
