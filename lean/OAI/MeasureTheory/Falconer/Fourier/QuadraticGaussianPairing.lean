import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Tactic.Ring

namespace OAI

namespace PlanarFalconer
open MeasureTheory
open scoped FourierTransform SchwartzMap RealInnerProductSpace

noncomputable def quadraticFourierKernel (a : ℂ) (ξ : ℝ) : ℂ :=
  ((Real.pi:ℂ)/a)^(1/2:ℂ) * Complex.exp (-((2*Real.pi*ξ:ℝ):ℂ)^2/(4*a))

 theorem fourier_quadraticGaussian {a : ℂ} (ha : 0 < a.re) (ξ : ℝ) :
    𝓕 (fun x : ℝ => Complex.exp (-a*(x:ℂ)^2)) ξ = quadraticFourierKernel a ξ := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  have he (x : ℝ) : ((-2*Real.pi*x*ξ:ℝ):ℂ)*Complex.I =
      Complex.I * ((-2*Real.pi*ξ:ℝ):ℂ) * (x:ℂ) := by push_cast; ring
  simp_rw [smul_eq_mul,he]
  rw [fourierIntegral_gaussian ha]
  unfold quadraticFourierKernel
  congr 3
  push_cast
  ring

 theorem quadraticGaussian_pairing {a : ℂ} (ha : 0 < a.re) (φ : 𝓢(ℝ,ℂ)) :
    (∫ x : ℝ, Complex.exp (-a*(x:ℂ)^2) * 𝓕 φ x) =
      ∫ ξ : ℝ, quadraticFourierKernel a ξ * φ ξ := by
  have hh := VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ ℝ) (μ := volume) (ν := volume)
    Real.continuous_fourierChar continuous_inner (integrable_cexp_neg_mul_sq ha) φ.integrable
  have hflip : (innerₗ ℝ : ℝ →ₗ[ℝ] ℝ →ₗ[ℝ] ℝ).flip = innerₗ ℝ := by
    ext; rfl
  rw [hflip] at hh
  have he : (∫ x : ℝ, Complex.exp (-a*(x:ℂ)^2) * 𝓕 φ x) =
      ∫ ξ : ℝ, 𝓕 (fun x : ℝ => Complex.exp (-a*(x:ℂ)^2)) ξ * φ ξ := by
    simpa only [smul_eq_mul] using! hh.symm
  rw [he]
  simp only [fourier_quadraticGaussian ha]

end PlanarFalconer

end OAI
