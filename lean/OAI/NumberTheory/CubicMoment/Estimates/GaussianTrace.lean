import OAI.NumberTheory.CubicGram.PeriodicPoisson
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

namespace OAI

/-! Gaussian Fourier kernels with the Eisenstein trace normalization. -/

noncomputable section
open scoped FourierTransform
open MeasureTheory
namespace CubicFirstMoment

lemma traceFourier_eq_fourier (f : ℂ → ℂ) (w : ℂ) :
    traceFourier f w = 𝓕 f (2*star w) := by
  rw [Real.fourier_eq,traceFourier]
  apply integral_congr_ae
  filter_upwards with z
  simp only [Circle.smul_def,smul_eq_mul]
  congr 2
  simp only [real_inner_eq_re_inner ℂ,RCLike.inner_apply,tracePair,
    Complex.star_def,RCLike.re_to_complex,Complex.mul_re,Complex.mul_im,
    Complex.conj_re,Complex.conj_im,Complex.re_ofNat,Complex.im_ofNat]
  congr 1
  ring

/-- The trace pairing doubles the usual Fourier frequency. -/
theorem traceFourier_gaussian {t : ℝ} (ht : 0 < t) (w : ℂ) :
    traceFourier (fun z : ℂ => Complex.exp (-(t:ℂ)*‖z‖^2)) w =
      (Real.pi/t:ℝ) * Complex.exp ((-4*Real.pi^2/t*Complex.normSq w:ℝ):ℂ) := by
  rw [traceFourier_eq_fourier]
  have h := fourier_gaussian_innerProductSpace (b := (t:ℂ))
    (by simpa using ht) (2*star w)
  rw [h]
  simp only [Complex.finrank_real_complex, Nat.cast_ofNat, div_self (by norm_num : (2:ℂ) ≠ 0),
    Complex.cpow_one]
  rw [Complex.ofReal_div]
  congr 2
  simp only [norm_mul,norm_star,Complex.normSq_eq_norm_sq]
  norm_num
  ring

end CubicFirstMoment

end

end OAI
