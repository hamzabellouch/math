import OAI.Analysis.OperatorAlgebra.SmallTimeOperatorAverage
import OAI.Analysis.ModularRecovery.SpectralCalculus
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

namespace OAI

/-! The integrable Schur factors obtained by normalized Gaussian averaging
of the dual characters. No limit or integrability is postulated. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace WeakPureInfiniteness

def gaussianSchurFactor (n : ℕ) (r : ℝ) : ℂ :=
  ∫ t : ℝ, (realGaussianDensity t : ℂ) *
    BoundedRecovery.spectralCharacter (-(t / (n + 1 : ℝ))) r

lemma gaussianSchurFactor_integrand (n : ℕ) (r : ℝ) :
    Integrable (fun t : ℝ => (realGaussianDensity t : ℂ) *
      BoundedRecovery.spectralCharacter (-(t / (n + 1 : ℝ))) r) := by
  have hi : Integrable (fun t : ℝ => (realGaussianDensity t : ℂ)) :=
    realGaussianDensity_integrable.ofReal
  have hc : Continuous (fun t : ℝ =>
      BoundedRecovery.spectralCharacter (-(t / (n + 1 : ℝ))) r) := by
    simp only [BoundedRecovery.spectralCharacter_apply]
    fun_prop
  apply hi.norm.mono' (hi.aestronglyMeasurable.mul hc.aestronglyMeasurable)
  filter_upwards [] with t
  simp only [Pi.mul_apply]
  rw [norm_mul, BoundedRecovery.spectralCharacter_norm, mul_one]

lemma gaussianSchurFactor_norm_le (n : ℕ) (r : ℝ) : ‖gaussianSchurFactor n r‖ ≤ 1 := by
  unfold gaussianSchurFactor
  calc
    _ ≤ ∫ t : ℝ, ‖(realGaussianDensity t : ℂ) *
        BoundedRecovery.spectralCharacter (-(t / (n + 1 : ℝ))) r‖ := norm_integral_le_integral_norm _
    _ = ∫ t : ℝ, realGaussianDensity t := by
      apply integral_congr_ae
      filter_upwards [] with t
      rw [norm_mul, BoundedRecovery.spectralCharacter_norm, mul_one, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (realGaussianDensity_nonneg t)]
    _ = 1 := realGaussianDensity_integral

lemma gaussianSchurFactor_formula (n : ℕ) (r : ℝ) :
    gaussianSchurFactor n r =
      ((Real.pi : ℂ) ^ (1 / 2 : ℂ) / (Real.sqrt Real.pi : ℂ)) *
        (Real.exp (-(r / (n + 1 : ℝ)) ^ 2 / 4) : ℂ) := by
  have he (t : ℝ) : (realGaussianDensity t : ℂ) *
      BoundedRecovery.spectralCharacter (-(t / (n + 1 : ℝ))) r =
      (Complex.exp (Complex.I * (-(r / (n + 1 : ℝ)) : ℂ) * t) *
        Complex.exp (-(1 : ℂ) * (t : ℂ) ^ 2)) / (Real.sqrt Real.pi : ℂ) := by
    have hc : BoundedRecovery.spectralCharacter (-(t / (n + 1 : ℝ))) r =
        Complex.exp (Complex.I * (-(r / (n + 1 : ℝ)) : ℂ) * t) := by
      change Complex.exp _ = Complex.exp _
      congr 1
      push_cast
      ring
    have hg : (realGaussianDensity t : ℂ) =
        Complex.exp (-(1 : ℂ) * (t : ℂ) ^ 2) / (Real.sqrt Real.pi : ℂ) := by
      simp only [realGaussianDensity, Complex.ofReal_div, Complex.ofReal_exp,
        Complex.ofReal_neg, Complex.ofReal_pow, neg_mul, one_mul]
    rw [hc, hg]
    ring
  unfold gaussianSchurFactor
  simp_rw [he]
  rw [integral_div, fourierIntegral_gaussian (by norm_num : (0 : ℝ) < (1 : ℂ).re)]
  simp only [div_one, mul_one]
  have hexp : Complex.exp (- (-(r / (n + 1 : ℝ)) : ℂ) ^ 2 / (4 : ℂ)) =
      (Real.exp (-(r / (n + 1 : ℝ)) ^ 2 / 4) : ℂ) := by
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  rw [hexp]
  ring

lemma gaussianSchurFactor_integrable (n : ℕ) : Integrable (gaussianSchurFactor n) := by
  have hi : Integrable (fun r : ℝ => Real.exp (-(1 / (4 * (n + 1 : ℝ) ^ 2)) * r ^ 2)) :=
    integrable_exp_neg_mul_sq (by positivity)
  have he (r : ℝ) : -(r / (n + 1 : ℝ)) ^ 2 / 4 =
      -(1 / (4 * (n + 1 : ℝ) ^ 2)) * r ^ 2 := by
    field_simp
  have hh := hi.ofReal.const_mul
    ((Real.pi : ℂ) ^ (1 / 2 : ℂ) / (Real.sqrt Real.pi : ℂ))
  exact hh.congr (ae_of_all _ fun r => by rw [gaussianSchurFactor_formula, he]; rfl)

lemma gaussianSchurFactor_continuous (n : ℕ) : Continuous (gaussianSchurFactor n) := by
  have he : gaussianSchurFactor n = fun r : ℝ =>
      ((Real.pi : ℂ) ^ (1 / 2 : ℂ) / (Real.sqrt Real.pi : ℂ)) *
        (Real.exp (-(r / (n + 1 : ℝ)) ^ 2 / 4) : ℂ) :=
    funext (gaussianSchurFactor_formula n)
  rw [he]
  fun_prop

end WeakPureInfiniteness

end

end OAI
