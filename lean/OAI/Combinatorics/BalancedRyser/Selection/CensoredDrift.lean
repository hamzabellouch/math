import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.Tactic

namespace OAI

open MeasureTheory Filter
open scoped ProbabilityTheory

namespace Balanced
open scoped _root_.Balanced

section
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [IsFiniteMeasure μ] {m : MeasurableSpace Ω} {Y Z : Ω → ℝ}
  {B : Set Ω} {M ε : ℝ}

theorem abs_condExp_sub_le_indicator
    (_hm : m ≤ mΩ) (hY : Integrable Y μ) (hZ : Integrable Z μ)
    (hB : @MeasurableSet Ω mΩ B)
    (hchange : ∀ᵐ ω ∂μ,
      |Y ω - Z ω| ≤ M * B.indicator (fun _ : Ω ↦ (1 : ℝ)) ω) :
    ∀ᵐ ω ∂μ, |μ[Y | m] ω - μ[Z | m] ω| ≤
      M * μ[B.indicator (fun _ : Ω ↦ (1 : ℝ)) | m] ω := by
  have hi : Integrable (B.indicator (fun _ : Ω ↦ (1 : ℝ))) μ :=
    (integrable_const 1).indicator hB
  have hnorm := norm_condExp_le (μ := μ) (m := m) (Y - Z)
  have hmono := condExp_mono (m := m) (hY.sub hZ).norm (hi.const_mul M)
    (hchange.mono fun ω hω ↦ by simpa only [Pi.sub_apply, Real.norm_eq_abs] using hω)
  have hsub := condExp_sub hY hZ m
  have hmul := condExp_smul (μ := μ) M (B.indicator (fun _ : Ω ↦ (1 : ℝ))) m
  filter_upwards [hnorm, hmono, hsub, hmul] with ω hn hb hs hc
  change μ[fun ω ↦ M * B.indicator (fun _ : Ω ↦ (1 : ℝ)) ω | m] ω =
    M * μ[B.indicator (fun _ : Ω ↦ (1 : ℝ)) | m] ω at hc
  change μ[Y - Z | m] ω = μ[Y | m] ω - μ[Z | m] ω at hs
  rw [hs, Real.norm_eq_abs] at hn
  exact hn.trans (hb.trans_eq hc)

theorem abs_condExp_sub_le_of_censor_probability
    (hm : m ≤ mΩ) (hY : Integrable Y μ) (hZ : Integrable Z μ)
    (hB : @MeasurableSet Ω mΩ B) (hM : 0 ≤ M)
    (hchange : ∀ᵐ ω ∂μ,
      |Y ω - Z ω| ≤ M * B.indicator (fun _ : Ω ↦ (1 : ℝ)) ω)
    (hprob : ∀ᵐ ω ∂μ, μ[B.indicator (fun _ : Ω ↦ (1 : ℝ)) | m] ω ≤ ε) :
    ∀ᵐ ω ∂μ, |μ[Y | m] ω - μ[Z | m] ω| ≤ M * ε := by
  filter_upwards [abs_condExp_sub_le_indicator hm hY hZ hB hchange, hprob]
    with ω hb hp
  exact hb.trans (mul_le_mul_of_nonneg_left hp hM)

theorem abs_condExp_censored_sub_le
    (hm : m ≤ mΩ) (hY : Integrable Y μ) (hZ : Integrable Z μ)
    (hB : @MeasurableSet Ω mΩ B) (hM : 0 ≤ M)
    (hchange : ∀ᵐ ω ∂μ, ω ∈ B → |Z ω - Y ω| ≤ M)
    (hprob : ∀ᵐ ω ∂μ, μ[B.indicator (fun _ : Ω ↦ (1 : ℝ)) | m] ω ≤ ε) :
    ∀ᵐ ω ∂μ, |μ[(fun ω ↦ B.indicator (fun ω ↦ Z ω - Y ω) ω + Y ω) | m] ω - μ[Y | m] ω| ≤ M * ε := by
  classical
  apply abs_condExp_sub_le_of_censor_probability hm (((hZ.sub hY).indicator hB).add hY) hY hB hM _ hprob
  filter_upwards [hchange] with ω hω
  by_cases hmem : ω ∈ B
  · simpa [hmem] using hω hmem
  · simp [hmem]

theorem condExp_censored_le_add
    (hm : m ≤ mΩ) (hY : Integrable Y μ) (hZ : Integrable Z μ)
    (hB : @MeasurableSet Ω mΩ B) (hM : 0 ≤ M)
    (hchange : ∀ᵐ ω ∂μ, ω ∈ B → |Z ω - Y ω| ≤ M)
    (hprob : ∀ᵐ ω ∂μ, μ[B.indicator (fun _ : Ω ↦ (1 : ℝ)) | m] ω ≤ ε) :
    ∀ᵐ ω ∂μ,
      μ[(fun ω ↦ B.indicator (fun ω ↦ Z ω - Y ω) ω + Y ω) | m] ω ≤
        μ[Y | m] ω + M * ε := by
  filter_upwards [abs_condExp_censored_sub_le hm hY hZ hB hM hchange hprob]
    with ω hω
  linarith [(abs_le.mp hω).2]

end
end Balanced

end OAI
