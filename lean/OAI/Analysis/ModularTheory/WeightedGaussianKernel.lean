import OAI.Analysis.ModularTheory.FourierOrbit

namespace OAI

/-! A normalized Gaussian whose angular Fourier transform is the bounded
regularization of exp(q/2). The normalization is chosen algebraically so no
choice of a real square root enters the later Tomita calculation. -/

noncomputable section
open MeasureTheory FourierTransform
open scoped ComplexOrder

namespace BoundedRecovery

def weightedGaussianKernel (a : ℝ) (t : ℝ) : ℂ :=
  ((((Real.pi : ℂ) / (a : ℂ)) ^ (1 / 2 : ℂ))⁻¹ * Complex.exp (a / 4 : ℂ)) *
    Complex.exp (-(a : ℂ) * t ^ 2 + Complex.I * a * t)

lemma weightedGaussianKernel_integrable (a : ℝ) (ha : 0 < a) :
    Integrable (weightedGaussianKernel a) := by
  unfold weightedGaussianKernel
  exact (spectralGaussian_integrable (a : ℂ) (Complex.I * a) (by exact ha)).const_mul _

lemma weightedGaussianKernel_fourier (a : ℝ) (ha : 0 < a) (q : ℝ) :
    (∫ t : ℝ, weightedGaussianKernel a t * spectralCharacter (-q) t) =
      Complex.exp ((q : ℂ) / 2 - (q : ℂ) ^ 2 / (4 * a)) := by
  have ha0 : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  have hp : ((Real.pi : ℂ) / (a : ℂ)) ^ (1 / 2 : ℂ) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr
      (Or.inl (div_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) ha0))
  have he : (a : ℂ) / 4 + (Complex.I * a - Complex.I * q) ^ 2 / (4 * a) =
      (q : ℂ) / 2 - (q : ℂ) ^ 2 / (4 * a) := by
    field_simp
    ring_nf
    simp only [Complex.I_sq]
    ring
  let C := (((Real.pi : ℂ) / (a : ℂ)) ^ (1 / 2 : ℂ))⁻¹ * Complex.exp (a / 4 : ℂ)
  have hi : (∫ t : ℝ, weightedGaussianKernel a t * spectralCharacter (-q) t) =
      C * ∫ t : ℝ, Complex.exp (-(a : ℂ) * t ^ 2 + (Complex.I * a) * t) *
        spectralCharacter (-q) t := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with t
    change (C * _) * _ = C * _
    ring
  rw [hi, spectralGaussian_fourier (a : ℂ) (Complex.I * a) (by exact ha)]
  dsimp only [C]
  calc
    _ = Complex.exp ((a : ℂ) / 4) *
        Complex.exp ((Complex.I * a - Complex.I * q) ^ 2 / (4 * a)) := by
      field_simp
    _ = _ := by rw [← Complex.exp_add, he]

lemma spectralFourierCutoff_weightedGaussian (a : ℝ) (ha : 0 < a)
    (χ : BoundedContinuousFunction ℝ ℂ) (hχ : HasCompactSupport (χ : ℝ → ℂ))
    (ω r : ℝ) :
    spectralFourierCutoff (weightedGaussianKernel a) χ ω r =
      χ r * Complex.exp (((ω + r : ℝ) : ℂ) / 2 -
        ((ω + r : ℝ) : ℂ) ^ 2 / (4 * a)) := by
  rw [spectralFourierCutoff_apply _ (weightedGaussianKernel_integrable a ha) χ hχ,
    weightedGaussianKernel_fourier a ha]

end BoundedRecovery

end

end OAI
