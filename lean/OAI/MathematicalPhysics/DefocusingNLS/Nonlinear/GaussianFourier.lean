import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.GaussianMoments
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.RandomSeries
import OAI.MathematicalPhysics.DefocusingNLS.Linear.SobolevWeights
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Probability.ProductMeasure

namespace OAI

/-!
# Almost-sure Sobolev summability of the Gaussian Fourier coefficients

The underlying independent coefficients are constructed using Mathlib's
countable product measure. Their weighted square sum is almost surely finite
at the exact threshold `α > k + 6` from Corollary 1.2.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace DefocusingNLS

/-- The standard independent complex Gaussian Fourier coefficients. -/
noncomputable def fourierGaussianLaw : Measure (frequencyLattice → ℂ) :=
  Measure.infinitePi (fun _ : frequencyLattice => complexGaussian (1 / 2))

instance : IsProbabilityMeasure fourierGaussianLaw := by
  unfold fourierGaussianLaw
  infer_instance

/-- Every coordinate has the standard complex Gaussian law. -/
theorem fourierGaussianLaw_map_eval (n : frequencyLattice) :
    fourierGaussianLaw.map (fun g => g n) = complexGaussian (1 / 2) :=
  Measure.infinitePi_map_eval _ n

theorem fourierGaussian_coordinate_second_moment (n : frequencyLattice) :
    (∫⁻ g, ENNReal.ofReal (Complex.normSq (g n)) ∂fourierGaussianLaw) = 1 := by
  rw [← lintegral_map (f := fun z : ℂ => ENNReal.ofReal (Complex.normSq z))
    (g := fun g : frequencyLattice → ℂ => g n) (by fun_prop) (by fun_prop),
    fourierGaussianLaw_map_eval]
  exact standard_complex_gaussian_normSq_moment

/-- The deterministic expected energy weight. -/
noncomputable def sobolevVariance (k α : ℝ) (n : frequencyLattice) : ℝ :=
  (1 + ‖n‖ ^ 2) ^ (k - α)

theorem sobolevVariance_nonneg (k α : ℝ) (n : frequencyLattice) :
    0 ≤ sobolevVariance k α n := by
  exact Real.rpow_nonneg (by positivity) _

/-- Almost-sure finite weighted Fourier energy. -/
theorem ae_summable_gaussian_sobolev_energy (k α : ℝ) (hα : k + 6 < α) :
    ∀ᵐ g ∂fourierGaussianLaw,
      Summable (fun n => sobolevVariance k α n * Complex.normSq (g n)) := by
  have hfinite := ae_tsum_lt_top_of_summable_expectations
    (μ := fourierGaussianLaw)
    (fun n g => ENNReal.ofReal (sobolevVariance k α n) *
      ENNReal.ofReal (Complex.normSq (g n)))
    (by intro n; fun_prop)
    (sobolevVariance k α) (summable_sobolev_variances k α hα)
    (by
      intro n
      rw [lintegral_const_mul _ (by fun_prop), fourierGaussian_coordinate_second_moment,
        mul_one])
  filter_upwards [hfinite] with g hg
  have hs := ENNReal.summable_toReal hg.ne
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sobolevVariance_nonneg k α _),
    ENNReal.toReal_ofReal (Complex.normSq_nonneg _)] using hs

/-- The normalized `H^k` coefficients, represented as an `ℓ²` sequence. -/
noncomputable def weightedGaussianCoefficient (k α : ℝ)
    (g : frequencyLattice → ℂ) (n : frequencyLattice) : ℂ :=
  Real.sqrt (sobolevVariance k α n) • g n

/-- These are exactly the `⟨n⟩^(k-α)`-weighted coordinates of the manuscript. -/
theorem weightedGaussianCoefficient_eq_rpow (k α : ℝ)
    (g : frequencyLattice → ℂ) (n : frequencyLattice) :
    weightedGaussianCoefficient k α g n =
      (1 + ‖n‖ ^ 2) ^ ((k - α) / 2) • g n := by
  unfold weightedGaussianCoefficient sobolevVariance
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity)]
  congr 2
  ring

theorem weightedGaussianCoefficient_norm_sq (k α : ℝ)
    (g : frequencyLattice → ℂ) (n : frequencyLattice) :
    ‖weightedGaussianCoefficient k α g n‖ ^ 2 =
      sobolevVariance k α n * Complex.normSq (g n) := by
  rw [weightedGaussianCoefficient, norm_smul, mul_pow,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    Real.sq_sqrt (sobolevVariance_nonneg k α n), Complex.normSq_eq_norm_sq]

/-- The weighted coefficient sequence lies in `ℓ²` almost surely. -/
theorem ae_mem_l2_gaussian_coefficients (k α : ℝ) (hα : k + 6 < α) :
    ∀ᵐ g ∂fourierGaussianLaw, Memℓp (weightedGaussianCoefficient k α g) 2 := by
  filter_upwards [ae_summable_gaussian_sobolev_energy k α hα] with g hg
  apply memℓp_gen
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two,
    weightedGaussianCoefficient_norm_sq] using hg

end DefocusingNLS

end OAI
