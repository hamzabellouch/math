import OAI.MeasureTheory.Falconer.Fourier.KernelFourierIdentity
import Mathlib.Analysis.Fourier.LpSpace

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set Filter
open scoped FourierTransform SchwartzMap

 theorem integrable_fourier_pairing (f : ℝ → ℂ) (hf : Integrable f)
    (g : 𝓢(ℝ, ℂ)) :
    (∫ x, g x * 𝓕 f x) = ∫ x, 𝓕 g x * f x := by
  have h := VectorFourier.integral_bilin_fourierIntegral_eq_flip
    (μ := volume) (ν := volume)
    (ContinuousLinearMap.mul ℂ ℂ) Real.continuous_fourierChar
    (by fun_prop : Continuous (fun p : ℝ × ℝ => innerₗ ℝ p.1 p.2)) hf g.integrable
  simpa only [ContinuousLinearMap.mul_apply', Real.fourier_eq,
    VectorFourier.fourierIntegral, LinearMap.flip_apply,
    innerₗ_apply_apply, real_inner_comm, SchwartzMap.fourier_coe, mul_comm] using h

 theorem fourier_L2_ae (f : ℝ → ℂ) (h1 : Integrable f) (h2 : MemLp f 2 volume) :
    (⇑(𝓕 (h2.toLp f) : Lp ℂ 2 volume) : ℝ → ℂ) =ᵐ[volume] 𝓕 f := by
  apply ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp (𝓕 (h2.toLp f))).locallyIntegrable (by norm_num))
    (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ h1).locallyIntegrable
  intro g hg hc
  let φ : 𝓢(ℝ, ℂ) := (hc.comp_left (map_zero Complex.ofRealCLM)).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp hg)
  have he := congrArg (fun T : 𝓢'(ℝ, ℂ) => T φ)
    (Lp.fourier_toTemperedDistribution_eq (h2.toLp f))
  simp only [TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply] at he
  have hf : (∫ x, 𝓕 φ x * (h2.toLp f) x) = ∫ x, 𝓕 φ x * f x :=
    integral_congr_ae (h2.coeFn_toLp.mono (fun x hx => by dsimp only; rw [hx]))
  have hh := integrable_fourier_pairing f h1 φ
  change (∫ x, (g x : ℂ) * (𝓕 (h2.toLp f) : Lp ℂ 2 volume) x) =
    ∫ x, (g x : ℂ) * 𝓕 f x
  exact (he.symm.trans hf).trans hh.symm

end PlanarFalconer

end OAI
