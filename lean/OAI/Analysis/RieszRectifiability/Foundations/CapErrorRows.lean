import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.CappedRieszKernel

namespace OAI

/-!
# Cap-error row bounds

The closed near-cap weight is constant on a closed ball and vanishes outside it.
Upper growth bounds give integrability of each row and a scale-independent integral bound.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function
open scoped ENNReal

theorem closedNearCapWeight_section {d : ℕ} (m : ℕ) (ε : ℝ) (x : Ambient d) :
    (fun y => closedNearCapWeight m ε (x, y)) =
      (closedBall x ε).indicator (fun _ => (ε ^ m)⁻¹) := by
  funext y
  classical
  by_cases hy : y ∈ closedBall x ε
  · simp only [closedNearCapWeight, indicator_of_mem (show (x, y) ∈ nearPairSet ε from hy),
      indicator_of_mem hy]
  · simp only [closedNearCapWeight, indicator_of_notMem (show (x, y) ∉ nearPairSet ε from hy),
      indicator_of_notMem hy]

theorem closedNearCapWeight_row_integrable_and_bound {d : ℕ} (m : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth m C μ)
    (ε : ℝ) (hε : 0 < ε) (x : Ambient d) :
    Integrable (fun y => closedNearCapWeight m ε (x, y)) μ ∧
      (∫ y, closedNearCapWeight m ε (x, y) ∂μ) ≤ C * 2 ^ m := by
  have hball : μ (closedBall x ε) ≤ ENNReal.ofReal (C * (2 * ε) ^ m) :=
    (measure_mono (closedBall_subset_ball (by linarith : ε < 2 * ε))).trans
      (hg.2 x (2 * ε) (by positivity))
  let : IsFiniteMeasure (μ.restrict (closedBall x ε)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hball.trans_lt ENNReal.ofReal_lt_top⟩
  have hreal : μ.real (closedBall x ε) ≤ C * (2 * ε) ^ m :=
    ENNReal.toReal_le_of_le_ofReal (mul_nonneg hg.1 (pow_nonneg (by positivity) _)) hball
  rw [closedNearCapWeight_section]
  refine ⟨(integrable_indicator_iff measurableSet_closedBall).mpr (integrable_const _), ?_⟩
  rw [integral_indicator measurableSet_closedBall, setIntegral_const, smul_eq_mul]
  calc
    μ.real (closedBall x ε) * (ε ^ m)⁻¹ ≤ (C * (2 * ε) ^ m) * (ε ^ m)⁻¹ :=
      mul_le_mul_of_nonneg_right hreal (by positivity)
    _ = C * 2 ^ m := by
      rw [mul_pow]
      have hne : ε ^ m ≠ 0 := pow_ne_zero _ hε.ne'
      field_simp

end

end RieszRectifiability

end OAI
