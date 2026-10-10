import OAI.Analysis.ModularRecovery.StrongIntegrals
import OAI.Analysis.ModularRecovery.SpectralCalculus
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

namespace OAI

/-! Fourier integration on compact spectral vectors. Compact support makes
the character orbit norm-continuous in the bounded functional calculus, so
integration can be transported through the actual calculus. This is the
local bridge for the weighted Tomita calculation, not a trace assumption. -/

noncomputable section
open MeasureTheory

namespace BoundedRecovery

lemma spectralCharacter_pair (ω r t : ℝ) :
    spectralCharacter (-ω) t * spectralCharacter (-t) r =
      spectralCharacter (-(ω + r)) t := by
  change Complex.exp _ * Complex.exp _ = Complex.exp _
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma spectralFourierWeight_integrable (k : ℝ → ℂ) (hk : Integrable k) (ω : ℝ) :
    Integrable (fun t => k t * spectralCharacter (-ω) t) := by
  apply hk.norm.mono'
    (hk.aestronglyMeasurable.mul (spectralCharacter (-ω)).continuous.aestronglyMeasurable)
  filter_upwards [] with t
  change ‖k t * spectralCharacter (-ω) t‖ ≤ ‖k t‖
  rw [norm_mul, spectralCharacter_norm, mul_one]

lemma spectralFourierCutoff_integrable (k : ℝ → ℂ) (hk : Integrable k)
    (χ : BoundedContinuousFunction ℝ ℂ) (hχ : HasCompactSupport (χ : ℝ → ℂ)) (ω : ℝ) :
    Integrable (fun t => (k t * spectralCharacter (-ω) t) • (spectralCharacter (-t) * χ)) := by
  apply integrable_smul_bounded_orbit (spectralFourierWeight_integrable k hk ω)
    ((RealSpectralCalculus.continuous_character_mul χ hχ).comp continuous_neg)
  intro t
  apply (BoundedContinuousFunction.norm_le (norm_nonneg χ)).mpr
  intro r
  change ‖spectralCharacter (-t) r * χ r‖ ≤ ‖χ‖
  rw [norm_mul, spectralCharacter_norm, one_mul]
  exact χ.norm_coe_le_norm r

def spectralFourierCutoff (k : ℝ → ℂ) (χ : BoundedContinuousFunction ℝ ℂ)
    (ω : ℝ) : BoundedContinuousFunction ℝ ℂ :=
  ∫ t, (k t * spectralCharacter (-ω) t) • (spectralCharacter (-t) * χ)

lemma spectralFourierCutoff_apply (k : ℝ → ℂ) (hk : Integrable k)
    (χ : BoundedContinuousFunction ℝ ℂ) (hχ : HasCompactSupport (χ : ℝ → ℂ))
    (ω r : ℝ) :
    spectralFourierCutoff k χ ω r =
      χ r * ∫ t, k t * spectralCharacter (-(ω + r)) t := by
  change (BoundedContinuousFunction.evalCLM ℂ r)
    (∫ t, (k t * spectralCharacter (-ω) t) • (spectralCharacter (-t) * χ)) = _
  rw [← (BoundedContinuousFunction.evalCLM ℂ r).integral_comp_comm
      (spectralFourierCutoff_integrable k hk χ hχ ω), ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with t
  change (k t * spectralCharacter (-ω) t) *
    (spectralCharacter (-t) r * χ r) = _
  rw [mul_assoc, ← mul_assoc (spectralCharacter (-ω) t), spectralCharacter_pair]
  ring

lemma spectralGaussian_integrable (a c : ℂ) (ha : 0 < a.re) :
    Integrable (fun t : ℝ => Complex.exp (-a * t ^ 2 + c * t)) := by
  simpa only [add_zero] using integrable_cexp_quadratic ha c 0

lemma spectralGaussian_fourier (a c : ℂ) (ha : 0 < a.re) (q : ℝ) :
    (∫ t : ℝ, Complex.exp (-a * t ^ 2 + c * t) * spectralCharacter (-q) t) =
      ((Real.pi : ℂ) / a) ^ (1 / 2 : ℂ) *
        Complex.exp ((c - Complex.I * q) ^ 2 / (4 * a)) := by
  have he : (fun t : ℝ => Complex.exp (-a * t ^ 2 + c * t) * spectralCharacter (-q) t) =
      fun t : ℝ => Complex.exp ((-a) * t ^ 2 + (c - Complex.I * q) * t + 0) := by
    funext t
    change Complex.exp _ * Complex.exp _ = Complex.exp _
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [he, integral_cexp_quadratic (show (-a).re < 0 by simpa only [Complex.neg_re,
    neg_lt_zero] using ha)]
  simp only [neg_neg, zero_sub, mul_neg, div_neg, neg_neg]

lemma spectralFourierCutoff_gaussian (a c : ℂ) (ha : 0 < a.re)
    (χ : BoundedContinuousFunction ℝ ℂ) (hχ : HasCompactSupport (χ : ℝ → ℂ))
    (ω r : ℝ) :
    spectralFourierCutoff (fun t : ℝ => Complex.exp (-a * t ^ 2 + c * t)) χ ω r =
      χ r * (((Real.pi : ℂ) / a) ^ (1 / 2 : ℂ) *
        Complex.exp ((c - Complex.I * (ω + r)) ^ 2 / (4 * a))) := by
  rw [spectralFourierCutoff_apply _ (spectralGaussian_integrable a c ha) χ hχ,
    spectralGaussian_fourier a c ha]
  simp only [Complex.ofReal_add]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma spectralFourierCutoff_calculus (D : RealSpectralCalculus H)
    (k : ℝ → ℂ) (hk : Integrable k)
    (χ : BoundedContinuousFunction ℝ ℂ) (hχ : HasCompactSupport (χ : ℝ → ℂ))
    (ω : ℝ) (v : H) :
    D.calculus (spectralFourierCutoff k χ ω) v =
      ∫ t, (k t * spectralCharacter (-ω) t) • D.unitary (-t) (D.calculus χ v) := by
  have hi := spectralFourierCutoff_integrable k hk χ hχ ω
  change D.calculusCLM (∫ t, (k t * spectralCharacter (-ω) t) •
    (spectralCharacter (-t) * χ)) v = _
  rw [← D.calculusCLM.integral_comp_comm hi,
    ContinuousLinearMap.integral_apply (D.calculusCLM.integrable_comp hi)]
  apply integral_congr_ae
  filter_upwards [] with t
  simp only [map_smul, smul_apply]
  change (k t * spectralCharacter (-ω) t) •
    D.calculus (spectralCharacter (-t) * χ) v = _
  rw [map_mul]
  rfl

end BoundedRecovery

end

end OAI
