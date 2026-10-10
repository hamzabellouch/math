import OAI.Analysis.ModularTheory.WeightedGaussianKernel
import OAI.Analysis.ModularTheory.SpectralShift

namespace OAI

/-! The weighted Fourier limit on the actual Tomita graph. At each frequency,
the regularized orbit converges to the half-graph image, with its explicit
exponential factor. The later L² passage still requires its integrable bound. -/

noncomputable section
open MeasureTheory Filter FourierTransform
open scoped Topology

namespace WeakPureInfiniteness
open BoundedRecovery

def modularTomitaKernel (n : ℕ) : ℝ → ℂ := weightedGaussianKernel ((n + 1 : ℝ) / 4)

lemma modularTomitaKernel_integrable (n : ℕ) : Integrable (modularTomitaKernel n) :=
  weightedGaussianKernel_integrable _ (by positivity)

lemma modularTomitaKernel_profile (n : ℕ) (s : ℝ)
    (χ : BoundedContinuousFunction ℝ ℂ) (hχ : HasCompactSupport (χ : ℝ → ℂ)) :
    spectralFourierCutoff (modularTomitaKernel n) χ s =
      χ * spectralTranslation s (modularHalfGaussian n) := by
  ext r
  rw [modularTomitaKernel, spectralFourierCutoff_weightedGaussian _ (by positivity) χ hχ]
  change χ r * Complex.exp _ = χ r * (Real.exp (-(r + s) ^ 2 / (n + 1) + (r + s) / 2) : ℂ)
  congr 1
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  have hn : (n : ℂ) + 1 ≠ 0 := by
    exact_mod_cast (show (n : ℝ) + 1 ≠ 0 by positivity)
  field_simp
  ring

lemma translatedHalfGaussian_eq (n : ℕ) (s : ℝ) :
    spectralTranslation s (modularHalfGaussian n) =
      (Real.exp (s / 2) : ℂ) • modularShiftedHalfGaussian n s := by
  unfold modularShiftedHalfGaussian
  rw [smul_smul]
  have he : (Real.exp (s / 2) : ℂ) * (Real.exp (-s / 2) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    simp only [add_neg_cancel, neg_div, Real.exp_zero, Complex.ofReal_one]
  rw [he, one_smul]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma modularTomitaKernel_calculus (D : RealSpectralCalculus H) (n : ℕ) (s : ℝ)
    (χ : BoundedContinuousFunction ℝ ℂ) (hχ : HasCompactSupport (χ : ℝ → ℂ)) (x : H) :
    D.calculus (spectralFourierCutoff (modularTomitaKernel n) χ s) x =
      (Real.exp (s / 2) : ℂ) •
        D.calculus (modularShiftedHalfGaussian n s) (D.calculus χ x) := by
  rw [modularTomitaKernel_profile n s χ hχ, mul_comm χ,
    translatedHalfGaussian_eq, smul_mul_assoc, map_smul, map_mul]
  rfl

lemma modularTomitaKernel_fourier_limit (D : RealSpectralCalculus H)
    {x y : H} (hxy : (x, y) ∈ D.halfGraph)
    (χ : BoundedContinuousFunction ℝ ℂ) (hχ : HasCompactSupport (χ : ℝ → ℂ))
    (ω : ℝ) :
    Tendsto (fun n => 𝓕 (fun t => modularTomitaKernel n t •
      D.unitary (-t) (D.calculus χ x)) ω) atTop
        (𝓝 ((Real.exp (Real.pi * ω) : ℂ) • D.calculus χ y)) := by
  have ht := (modularShiftedHalfGaussian_strong D
    (D.halfGraph_calculus hxy χ) (2 * Real.pi * ω)).const_smul
      (Real.exp ((2 * Real.pi * ω) / 2) : ℂ)
  have he : (2 * Real.pi * ω) / 2 = Real.pi * ω := by ring
  simp_rw [fourier_spectral_orbit D _ (modularTomitaKernel_integrable _) χ hχ x,
    modularTomitaKernel_calculus D _ _ χ hχ x]
  simpa only [he] using ht

end WeakPureInfiniteness

end

end OAI
