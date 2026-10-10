import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.ShellHeightL1
import OAI.Analysis.RieszRectifiability.Kernel.MeanCorrectionAdmissible

namespace OAI

/-!
# Local moments of bounded tests

Compact support makes products of mean-corrected tests with continuous height
functions integrable. Local mass and square-integrability bounds then control
the absolute moments of bounded tests and their height-weighted products.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set Function Filter Topology
open scoped NNReal ENNReal

theorem meanCorrection_height_product_integrable {d : ℕ}
    (μ : Measure (Ambient d)) [IsFiniteMeasureOnCompacts μ]
    (φ η w : Ambient d → ℝ) (hφ : Continuous φ) (hη : Continuous η) (hw : Continuous w)
    (hcφ : HasCompactSupport φ) (hcη : HasCompactSupport η) :
    Integrable (fun x => meanCorrection μ φ η x * w x) μ := by
  have hc : HasCompactSupport (meanCorrection μ φ η) := hcφ.sub hcη.mul_left
  exact ((hφ.sub (continuous_const.mul hη)).mul hw).integrable_of_hasCompactSupport hc.mul_right

theorem bounded_test_local_moment_bounds {d : ℕ}
    (ν : Measure (Ambient d)) [IsFiniteMeasure ν]
    (w φ : Ambient d → ℝ) (hw : MemLp w 2 ν) (hφm : Measurable φ)
    (B : ℝ≥0) (hB : ∀ x, |φ x| ≤ (B : ℝ))
    (M : ℝ) (hM : 0 ≤ M) (hmass : ν.real univ ≤ M) (hsecond : (∫ x, w x ^ 2 ∂ν) ≤ M) :
    Integrable φ ν ∧ Integrable (fun x => φ x * w x) ν ∧
      (∫ x, |φ x| ∂ν) ≤ (B : ℝ) * M ∧ (∫ x, |φ x * w x| ∂ν) ≤ (B : ℝ) * M := by
  have hφL2 : MemLp φ 2 ν := MemLp.of_bound hφm.aestronglyMeasurable (B : ℝ)
    (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using! hB x)
  have hiφ := hφL2.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hprod : MemLp (fun x => φ x * w x) 1 ν := hφL2.mul hw
  have hiprod := memLp_one_iff_integrable.mp hprod
  refine ⟨hiφ, hiprod, ?_, ?_⟩
  · calc
      _ ≤ ∫ _, (B : ℝ) ∂ν := integral_mono_ae hiφ.abs (integrable_const _)
        (Eventually.of_forall hB)
      _ = (B : ℝ) * ν.real univ := by rw [integral_const, smul_eq_mul, mul_comm]
      _ ≤ _ := mul_le_mul_of_nonneg_left hmass B.coe_nonneg
  · have hwI := hw.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    have hwB : (∫ x, |w x| ∂ν) ≤ M := by
      simpa only [one_pow, mul_one] using! integral_abs_le_of_mass_second_moment ν w hw
        M 1 hM (by norm_num) hmass (by simpa only [one_pow, mul_one] using! hsecond)
    calc
      _ ≤ ∫ x, (B : ℝ) * |w x| ∂ν := by
        apply integral_mono_ae hiprod.abs (hwI.abs.const_mul (B : ℝ))
        exact Eventually.of_forall fun x => by
          change |φ x * w x| ≤ (B : ℝ) * |w x|
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_right (hB x) (abs_nonneg _)
      _ = (B : ℝ) * (∫ x, |w x| ∂ν) := integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hwB B.coe_nonneg

end

end RieszRectifiability

end OAI
