import OAI.NumberTheory.CubicMoment.Estimates.HarmonicGaussianFourier

namespace OAI

/-! The conjugate harmonic monomials, obtained by the measure-preserving
complex reflection. -/
noncomputable section
open scoped SchwartzMap FourierTransform
namespace CubicFirstMoment

def antiHarmonicGaussian (a : ℝ) (ha : 0 < a) (n : ℕ) : 𝓢(ℂ,ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ Complex.conjLIE.toContinuousLinearEquiv
    (harmonicGaussian a ha n)

@[simp] lemma antiHarmonicGaussian_apply (a : ℝ) (ha : 0 < a) (n : ℕ) (z : ℂ) :
    antiHarmonicGaussian a ha n z = (star z)^n*(radialGaussian a z:ℂ) := by
  simp [antiHarmonicGaussian,harmonicGaussian_apply,radialGaussian]

lemma antiHarmonicGaussian_traceFourier (a : ℝ) (ha : 0 < a) (n : ℕ) (w : ℂ) :
    traceFourier (antiHarmonicGaussian a ha n) w =
      (-2*(Real.pi:ℂ)*Complex.I/(a:ℂ))^n*w^n*
        (Real.pi/a:ℝ)*(Real.exp (-4*Real.pi^2/a*Complex.normSq w):ℝ) := by
  have he : (antiHarmonicGaussian a ha n : ℂ → ℂ) =
      (harmonicGaussian a ha n) ∘ Complex.conjLIE := rfl
  rw [traceFourier_eq_fourier,he,Real.fourier_comp_linearIsometry]
  have h := harmonicGaussian_traceFourier a ha n (star w)
  rw [traceFourier_eq_fourier] at h
  simpa only [Complex.conjLIE_apply,map_mul,map_ofNat,star_star,Complex.star_def,Complex.conj_conj,
    Complex.normSq_conj] using h

end CubicFirstMoment

end

end OAI
