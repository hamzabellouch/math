import OAI.Analysis.ModularTheory.SpectralFourier

namespace OAI

/-! The actual vector-valued Fourier transform of a compact spectral orbit.
The frequency shift and the factor 2π are explicit, connecting the spectral
Gaussian calculation to the regular representation used for the core. -/

noncomputable section
open MeasureTheory FourierTransform

namespace BoundedRecovery

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma integrable_spectral_orbit (D : RealSpectralCalculus H)
    (k : ℝ → ℂ) (hk : Integrable k) (v : H) :
    Integrable (fun t => k t • D.unitary (-t) v) :=
  integrable_smul_bounded_orbit hk
    ((D.continuous_unitary_apply v).comp continuous_neg)
    (fun t => (D.norm_unitary_apply (-t) v).le)

lemma fourier_spectral_orbit (D : RealSpectralCalculus H)
    (k : ℝ → ℂ) (hk : Integrable k)
    (χ : BoundedContinuousFunction ℝ ℂ) (hχ : HasCompactSupport (χ : ℝ → ℂ))
    (v : H) (ω : ℝ) :
    𝓕 (fun t => k t • D.unitary (-t) (D.calculus χ v)) ω =
      D.calculus (spectralFourierCutoff k χ (2 * Real.pi * ω)) v := by
  rw [Real.fourier_real_eq_integral_exp_smul, spectralFourierCutoff_calculus D k hk χ hχ]
  apply integral_congr_ae
  filter_upwards [] with t
  rw [smul_smul]
  congr 1
  have h : Complex.exp ((-2 * Real.pi * t * ω : ℝ) * Complex.I) =
      spectralCharacter (-(2 * Real.pi * ω)) t := by
    change Complex.exp _ = Complex.exp _
    congr 1
    push_cast
    ring
  rw [h, mul_comm]

lemma fourier_gaussian_spectral_orbit (D : RealSpectralCalculus H)
    (a c : ℂ) (ha : 0 < a.re)
    (χ : BoundedContinuousFunction ℝ ℂ) (hχ : HasCompactSupport (χ : ℝ → ℂ))
    (v : H) (ω : ℝ) :
    𝓕 (fun t : ℝ => Complex.exp (-a * t ^ 2 + c * t) •
      D.unitary (-t) (D.calculus χ v)) ω =
      D.calculus (spectralFourierCutoff
        (fun t : ℝ => Complex.exp (-a * t ^ 2 + c * t)) χ (2 * Real.pi * ω)) v :=
  fourier_spectral_orbit D _ (spectralGaussian_integrable a c ha) χ hχ v ω

end BoundedRecovery

end

end OAI
