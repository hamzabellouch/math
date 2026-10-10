import Mathlib
import OAI.Analysis.RieszRectifiability.Limits.CompactWeakConvergence
import OAI.Analysis.RieszRectifiability.Kernel.LipschitzTests

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function Filter Topology
open scoped NNReal CompactlySupported

theorem meanCorrection_restrict_of_support {d : ℕ} (μ : Measure (Ambient d))
    (s : Set (Ambient d)) (φ η : Ambient d → ℝ)
    (hφ : ∀ x ∉ s, φ x = 0) (hη : ∀ x ∉ s, η x = 0) :
    meanCorrection (μ.restrict s) φ η = meanCorrection μ φ η := by
  unfold meanCorrection
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hφ,
    setIntegral_eq_integral_of_forall_compl_eq_zero hη]

theorem compact_meanCorrection_admissible {d : ℕ}
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, IsFiniteMeasureOnCompacts (μ j)]
    (hlocal : CompactTestConvergence μ ν)
    (φ η : Ambient d → ℝ) (Lφ Lη Bφ Bη : ℝ≥0)
    (hφ : LipschitzWith Lφ φ) (hη : LipschitzWith Lη η)
    (hcφ : HasCompactSupport φ) (hcη : HasCompactSupport η)
    (hBφ : ∀ x, |φ x| ≤ (Bφ : ℝ)) (hBη : ∀ x, |η x| ≤ (Bη : ℝ))
    (hmean : (∫ x, φ x ∂ν) = 0) (hbump : (∫ x, η x ∂ν) ≠ 0) :
    Tendsto (fun j => (∫ x, φ x ∂μ j) / (∫ x, η x ∂μ j)) atTop (𝓝 0) ∧
      ∀ᶠ j in atTop,
        (∫ x, η x ∂μ j) ≠ 0 ∧
        Integrable (meanCorrection (μ j) φ η) (μ j) ∧
        (∫ x, meanCorrection (μ j) φ η x ∂μ j) = 0 ∧
        LipschitzWith (Lφ + Lη) (meanCorrection (μ j) φ η) ∧
        (∀ x, |meanCorrection (μ j) φ η x| ≤ ((Bφ + Bη : ℝ≥0) : ℝ)) ∧
        HasCompactSupport (meanCorrection (μ j) φ η) := by
  have hφlim := hlocal (⟨⟨φ, hφ.continuous⟩, hcφ⟩ : C_c(Ambient d, ℝ))
  have hηlim := hlocal (⟨⟨η, hη.continuous⟩, hcη⟩ : C_c(Ambient d, ℝ))
  change Tendsto (fun j => ∫ x, φ x ∂μ j) atTop (𝓝 (∫ x, φ x ∂ν)) at hφlim
  change Tendsto (fun j => ∫ x, η x ∂μ j) atTop (𝓝 (∫ x, η x ∂ν)) at hηlim
  rw [hmean] at hφlim
  have hc := meanCorrection_coefficient_tendsto_zero μ φ η _ hbump hφlim hηlim
  refine ⟨hc, ?_⟩
  have hcabs : Tendsto (fun j => |(∫ x, φ x ∂μ j) / (∫ x, η x ∂μ j)|) atTop (𝓝 0) := by
    simpa only [Real.norm_eq_abs, norm_zero] using! hc.norm
  filter_upwards [hηlim.eventually (eventually_ne_nhds hbump),
    hcabs.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with j hηne hcoef
  have hiφ : Integrable φ (μ j) := hφ.continuous.integrable_of_hasCompactSupport hcφ
  have hiη : Integrable η (μ j) := hη.continuous.integrable_of_hasCompactSupport hcη
  refine ⟨hηne, meanCorrection_integrable (μ j) φ η hiφ hiη,
    meanCorrection_integral_zero (μ j) φ η hiφ hiη hηne, ?_, ?_, ?_⟩
  · apply (meanCorrection_lipschitz (μ j) hφ hη).weaken
    apply add_le_add le_rfl
    have hcNN : ‖(∫ x, φ x ∂μ j) / (∫ x, η x ∂μ j)‖₊ ≤ 1 := by
      apply NNReal.coe_le_coe.mp
      simpa only [coe_nnnorm, Real.norm_eq_abs, NNReal.coe_one] using! hcoef.le
    simpa only [one_mul] using! mul_le_mul_of_nonneg_right hcNN (zero_le)
  · intro x
    unfold meanCorrection
    calc
      _ ≤ |φ x| + |(∫ y, φ y ∂μ j) / (∫ y, η y ∂μ j)| * |η x| := by
        simpa only [sub_zero, zero_sub, abs_neg, abs_mul] using! abs_sub_le (φ x) 0
          (((∫ y, φ y ∂μ j) / (∫ y, η y ∂μ j)) * η x)
      _ ≤ (Bφ : ℝ) + 1 * (Bη : ℝ) :=
        add_le_add (hBφ x) (mul_le_mul hcoef.le (hBη x) (abs_nonneg _) (by norm_num))
      _ = _ := by rw [one_mul, NNReal.coe_add]
  · exact hcφ.sub hcη.mul_left

theorem meanCorrection_zero_off_common_support {d : ℕ} (μ : Measure (Ambient d))
    (φ η : Ambient d → ℝ) (s : Set (Ambient d))
    (hφ : ∀ x ∉ s, φ x = 0) (hη : ∀ x ∉ s, η x = 0) :
    ∀ x ∉ s, meanCorrection μ φ η x = 0 := by
  intro x hx
  simp only [meanCorrection, hφ x hx, hη x hx, mul_zero, sub_zero]

end

end RieszRectifiability

end OAI
