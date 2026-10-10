import Mathlib.Analysis.Fourier.LpSpace

namespace OAI

/-! Agreement of the classical integral Fourier transform with the
library L² transform, in the integrable case needed for finite windows. -/

namespace TwoPointCorrelations

open MeasureTheory FourierTransform
open scoped SchwartzMap

theorem mrt_fourier_toL2 {f : ℝ → ℂ} (hf : Integrable f)
    (hf₂ : MemLp f 2) (hF₂ : MemLp (𝓕 f) 2) :
    𝓕 hf₂.toLp = hF₂.toLp := by
  apply (LinearMap.ker_eq_bot.mp
    (Lp.ker_toTemperedDistributionCLM_eq_bot (F := ℂ) (E := ℝ) (μ := volume) (p := 2)))
  change Lp.toTemperedDistribution (𝓕 hf₂.toLp) =
    Lp.toTemperedDistribution hF₂.toLp
  rw [← Lp.fourier_toTemperedDistribution_eq]
  ext g
  rw [TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply,
    Lp.toTemperedDistribution_apply]
  calc
    _ = ∫ x : ℝ, (𝓕 g) x • f x := by
      apply integral_congr_ae
      filter_upwards [hf₂.coeFn_toLp] with x hx
      rw [hx]
    _ = ∫ x : ℝ, g x • (𝓕 f) x := by
      simpa using! (VectorFourier.integral_fourierIntegral_smul_eq_flip
        (L := innerₗ ℝ) Real.continuous_fourierChar continuous_inner g.integrable hf)
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hF₂.coeFn_toLp] with x hx
      rw [hx]

lemma mrt_toL2_norm_sq {f : ℝ → ℂ} (hf₂ : MemLp f 2) :
    ‖hf₂.toLp‖ ^ 2 = ∫ x : ℝ, ‖f x‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf₂.coeFn_toLp] with x hx
  rw [hx, real_inner_self_eq_norm_sq]

theorem mrt_plancherel {f : ℝ → ℂ} (hf : Integrable f)
    (hf₂ : MemLp f 2) (hF₂ : MemLp (𝓕 f) 2) :
    (∫ x : ℝ, ‖𝓕 f x‖ ^ 2) = ∫ x : ℝ, ‖f x‖ ^ 2 := by
  rw [← mrt_toL2_norm_sq hF₂, ← mrt_fourier_toL2 hf hf₂ hF₂,
    Lp.norm_fourier_eq, mrt_toL2_norm_sq hf₂]

end TwoPointCorrelations

end OAI
