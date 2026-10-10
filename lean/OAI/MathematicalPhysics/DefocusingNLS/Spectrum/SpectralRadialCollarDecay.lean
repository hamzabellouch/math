import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRadialLocalEnergy

namespace OAI

/-! The derivative energy in a shrinking collar tends to zero. -/

open Set MeasureTheory Filter Topology
namespace DefocusingNLS

theorem spectralRadialIntervalMask_tendsto_zero (R l : ℝ) (U : ℕ → ℝ)
    (hU : Tendsto U atTop (𝓝 l)) (u : SpectralRadialL2 R) :
    Tendsto (fun n => spectralRadialIntervalMask R l (U n) u) atTop (𝓝 0) := by
  let f := fun n : ℕ => (Icc l (U n)).indicator (fun s : ℝ => ‖u s‖^2)
  have hint : Integrable (fun s : ℝ => ‖u s‖^2) (radialPressureMeasure R) :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable u)).mp (Lp.memLp u)
  have hm (n : ℕ) : AEStronglyMeasurable (f n) (radialPressureMeasure R) := by
    exact ((Lp.aestronglyMeasurable u).norm.pow 2).indicator measurableSet_Icc
  have hb (n : ℕ) : ∀ᵐ s ∂radialPressureMeasure R, ‖f n s‖ ≤ ‖u s‖^2 := by
    apply Filter.Eventually.of_forall
    intro s
    by_cases hs : s ∈ Icc l (U n) <;> simp [f,hs]
  have hp : ∀ᵐ s ∂radialPressureMeasure R, Tendsto (fun n => f n s) atTop (𝓝 0) := by
    have hn : ∀ᵐ s ∂radialPressureMeasure R, s ≠ l := by
      simp only [ae_iff]
      simpa using spectralRadialMeasure_singleton R l
    filter_upwards [hn] with s hs
    rcases lt_or_gt_of_ne hs with hsl | hls
    · have he : ∀ n, f n s=0 := by
        intro n
        simp [f,not_le.mpr hsl]
      simpa only [he] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
    · apply tendsto_const_nhds.congr'
      filter_upwards [hU.eventually (Iio_mem_nhds hls)] with n hn
      simp [f,not_le.mpr hn]
  have hi : Tendsto (fun n => ∫ s, f n s ∂radialPressureMeasure R) atTop (𝓝 0) := by
    simpa only [integral_zero] using
      tendsto_integral_of_dominated_convergence (fun s => ‖u s‖^2) hm hint hb hp
  have hsq : Tendsto (fun n => ‖spectralRadialIntervalMask R l (U n) u‖^2) atTop (𝓝 0) := by
    simpa only [spectralRadialIntervalMask_norm_sq,integral_indicator measurableSet_Icc,f] using hi
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hh := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  simpa only [Function.comp_def,Real.sqrt_sq_eq_abs,abs_norm,Real.sqrt_zero] using hh

end DefocusingNLS

end OAI
