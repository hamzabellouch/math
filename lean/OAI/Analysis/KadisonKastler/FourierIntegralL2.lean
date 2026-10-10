import Mathlib.Analysis.Fourier.LpSpace

namespace OAI

/-! # Agreement of the integral and Hilbert-space Fourier transforms

The reproducing kernels used by Hardy evaluation are integrable square-integrable
functions, rather than Schwartz functions. This bridge identifies their explicit
integral transforms with the existing unitary Fourier transform.
-/

namespace KadisonKastler

open MeasureTheory SchwartzMap
open scoped FourierTransform

noncomputable section

/-- An integrable scalar function whose Fourier transform is square integrable
has the same transform in the concrete `L²` Fourier representation. -/
theorem fourier_toLp_of_integrable {f : ℝ → ℂ} (hf : Integrable f)
    (hf2 : MemLp f 2) (hF2 : MemLp (𝓕 f) 2) :
    𝓕 (hf2.toLp f) = hF2.toLp (𝓕 f) := by
  apply (LinearMap.ker_eq_bot.mp
    (Lp.ker_toTemperedDistributionCLM_eq_bot (F := ℂ) (μ := volume) (p := 2)))
  change Lp.toTemperedDistribution (𝓕 (hf2.toLp f)) =
    Lp.toTemperedDistribution (hF2.toLp (𝓕 f))
  rw [← Lp.fourier_toTemperedDistribution_eq]
  ext g
  rw [TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply,
    Lp.toTemperedDistribution_apply]
  have hl : (∫ x, (𝓕 g) x • hf2.toLp f x) = ∫ x, (𝓕 g) x • f x := by
    apply integral_congr_ae
    filter_upwards [hf2.coeFn_toLp] with x hx
    rw [hx]
  have hr : (∫ x, g x • hF2.toLp (𝓕 f) x) = ∫ x, g x • (𝓕 f) x := by
    apply integral_congr_ae
    filter_upwards [hF2.coeFn_toLp] with x hx
    rw [hx]
  rw [hl, hr]
  simpa only [SchwartzMap.fourier_coe, Real.fourier_eq, VectorFourier.fourierIntegral,
    LinearMap.flip_apply, innerₗ_apply_apply, real_inner_comm, smul_eq_mul] using!
    (VectorFourier.integral_fourierIntegral_smul_eq_flip
    (μ := volume) (ν := volume) (L := innerₗ ℝ) Real.continuous_fourierChar (by fun_prop) g.integrable hf)

/-- An integrable scalar function whose Fourier transform is square integrable
has the same transform in the concrete `L²` Fourier representation. -/
theorem fourierInv_toLp_of_integrable {f : ℝ → ℂ} (hf : Integrable f)
    (hf2 : MemLp f 2) (hF2 : MemLp (𝓕⁻ f) 2) :
    𝓕⁻ (hf2.toLp f) = hF2.toLp (𝓕⁻ f) := by
  apply (LinearMap.ker_eq_bot.mp
    (Lp.ker_toTemperedDistributionCLM_eq_bot (F := ℂ) (μ := volume) (p := 2)))
  change Lp.toTemperedDistribution (𝓕⁻ (hf2.toLp f)) =
    Lp.toTemperedDistribution (hF2.toLp (𝓕⁻ f))
  rw [← Lp.fourierInv_toTemperedDistribution_eq]
  ext g
  rw [TemperedDistribution.fourierInv_apply, Lp.toTemperedDistribution_apply,
    Lp.toTemperedDistribution_apply]
  have hl : (∫ x, (𝓕⁻ g) x • hf2.toLp f x) = ∫ x, (𝓕⁻ g) x • f x := by
    apply integral_congr_ae
    filter_upwards [hf2.coeFn_toLp] with x hx
    rw [hx]
  have hr : (∫ x, g x • hF2.toLp (𝓕⁻ f) x) = ∫ x, g x • (𝓕⁻ f) x := by
    apply integral_congr_ae
    filter_upwards [hF2.coeFn_toLp] with x hx
    rw [hx]
  rw [hl, hr]
  simpa only [SchwartzMap.fourierInv_coe, Real.fourierInv_eq, VectorFourier.fourierIntegral,
    LinearMap.flip_apply, LinearMap.neg_apply, neg_neg, innerₗ_apply_apply, real_inner_comm, smul_eq_mul] using!
    (VectorFourier.integral_fourierIntegral_smul_eq_flip
    (μ := volume) (ν := volume) (L := -innerₗ ℝ) Real.continuous_fourierChar (by fun_prop) g.integrable hf)


end

end KadisonKastler

end OAI
