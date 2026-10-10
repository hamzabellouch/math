import OAI.MeasureTheory.Falconer.Shells.SmoothShellPartition

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set Filter
open scoped Topology

theorem sourceShellLowpass_abs_le (n : ℕ) (r : ℝ) : |sourceShellLowpass n r| ≤ 1 := by
  rw [abs_of_nonneg (show 0 ≤ sourceShellLowpass n r from sourceShellBump.nonneg)]
  exact sourceShellBump.le_one

theorem sourceShellLowpass_fourier_test (τ : Measure ℝ) [IsFiniteMeasure τ]
    (f : ℝ → ℂ) (hf : Integrable f) :
    Tendsto (fun n => ∫ r, sourceShellLowpass n r • (charFun τ r * f r)) atTop
      (𝓝 (∫ r, charFun τ r * f r)) := by
  have hm (n : ℕ) : AEStronglyMeasurable
      (fun r => sourceShellLowpass n r • (charFun τ r * f r)) volume :=
    (sourceShellLowpass_smooth n).continuous.aestronglyMeasurable.smul
      (continuous_charFun.aestronglyMeasurable.mul hf.aestronglyMeasurable)
  have hb (n : ℕ) : ∀ᵐ r ∂volume,
      ‖sourceShellLowpass n r • (charFun τ r * f r)‖ ≤ τ.real univ * ‖f r‖ := by
    filter_upwards with r
    rw [norm_smul, Real.norm_eq_abs, norm_mul]
    calc
      |sourceShellLowpass n r| * (‖charFun τ r‖ * ‖f r‖) ≤
          1 * (‖charFun τ r‖ * ‖f r‖) :=
        mul_le_mul_of_nonneg_right (sourceShellLowpass_abs_le n r) (by positivity)
      _ ≤ τ.real univ * ‖f r‖ := by
        rw [one_mul]
        exact mul_le_mul_of_nonneg_right (norm_charFun_le r) (norm_nonneg _)
  have hp : ∀ᵐ r ∂volume,
      Tendsto (fun n => sourceShellLowpass n r • (charFun τ r * f r)) atTop
        (𝓝 (charFun τ r * f r)) := by
    filter_upwards with r
    simpa using (sourceShellLowpass_tendsto r).smul (tendsto_const_nhds (x := charFun τ r * f r))
  exact tendsto_integral_of_dominated_convergence (fun r => τ.real univ * ‖f r‖)
    hm (hf.norm.const_mul _) hb hp

theorem sourceShellPartition_fourier_test (τ : Measure ℝ) [IsFiniteMeasure τ]
    (f : ℝ → ℂ) (hf : Integrable f) :
    Tendsto (fun n => ∫ r, (sourceShellLowpass 0 r +
      ∑ k ∈ Finset.range n, sourceShellBand k r) • (charFun τ r * f r)) atTop
      (𝓝 (∫ r, charFun τ r * f r)) := by
  simpa only [sourceShellPartition_telescope] using sourceShellLowpass_fourier_test τ f hf

end PlanarFalconer

end OAI
