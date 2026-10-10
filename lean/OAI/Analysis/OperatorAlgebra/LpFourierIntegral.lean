import Mathlib.Analysis.Fourier.LpSpace

namespace OAI

/-! Compatibility of the L² Fourier transform with the Bochner integral
when both the function and its classical transform are square integrable.
This is used for the regularized modular orbits. -/

noncomputable section
open MeasureTheory FourierTransform

namespace WeakPureInfiniteness

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma fourier_toLp_of_integrable (f : ℝ → H) (hi : Integrable f)
    (hf : MemLp f 2 (volume : Measure ℝ))
    (hF : MemLp (𝓕 f) 2 (volume : Measure ℝ)) :
    𝓕 (hf.toLp f) = hF.toLp (𝓕 f) := by
  apply LinearMap.ker_eq_bot.mp
    (Lp.ker_toTemperedDistributionCLM_eq_bot (F := H) (μ := volume) (p := 2))
  change Lp.toTemperedDistribution (𝓕 (hf.toLp f)) =
    Lp.toTemperedDistribution (hF.toLp (𝓕 f))
  rw [← Lp.fourier_toTemperedDistribution_eq]
  ext φ
  rw [TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply,
    Lp.toTemperedDistribution_apply]
  calc
    (∫ t : ℝ, (𝓕 φ) t • (hf.toLp f) t) = ∫ t : ℝ, (𝓕 φ) t • f t := by
      apply integral_congr_ae
      filter_upwards [hf.coeFn_toLp] with t ht
      rw [ht]
    _ = ∫ ω : ℝ, φ ω • (𝓕 f) ω := by
      simpa using! VectorFourier.integral_fourierIntegral_smul_eq_flip
        (L := innerₗ ℝ) Real.continuous_fourierChar continuous_inner φ.integrable hi
    _ = ∫ ω : ℝ, φ ω • (hF.toLp (𝓕 f)) ω := by
      apply integral_congr_ae
      filter_upwards [hF.coeFn_toLp] with ω hω
      rw [hω]

end WeakPureInfiniteness

end

end OAI
