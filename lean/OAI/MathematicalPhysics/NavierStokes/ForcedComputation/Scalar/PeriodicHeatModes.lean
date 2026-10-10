import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.TorusHeatGaussianBound
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.Basic

namespace OAI

/-! Polynomially weighted Fourier modes for the classical periodic heat
solution. The positive-time Gaussian majorants are explicit. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows Set Complex
open scoped ContDiff BigOperators

def heatModeLinear (n : ℤ) : (ℝ × ℝ) →L[ℝ] ℂ :=
  (-4 * Real.pi ^ 2 * (n : ℝ) ^ 2) •
      (Complex.ofRealCLM.comp (ContinuousLinearMap.fst ℝ ℝ ℝ)) +
    (2 * Real.pi * (n : ℝ)) •
      (Complex.I • (Complex.ofRealCLM.comp (ContinuousLinearMap.snd ℝ ℝ ℝ)))

def heatMode (k : ℕ) (n : ℤ) (p : ℝ × ℝ) : ℂ :=
  (n : ℂ) ^ k * Complex.exp (heatModeLinear n p)

def heatModeBound (k : ℕ) (T : ℝ) (n : ℤ) : ℝ :=
  |(n : ℝ)| ^ k * Real.exp (-4 * Real.pi ^ 2 * (n : ℝ) ^ 2 * T)

theorem heatModeLinear_re (n : ℤ) (p : ℝ × ℝ) :
    (heatModeLinear n p).re = -4 * Real.pi ^ 2 * (n : ℝ) ^ 2 * p.1 := by
  simp [heatModeLinear, -Complex.ofReal_pow, Complex.mul_re, Complex.mul_im, mul_assoc]

theorem heatMode_smooth (k : ℕ) (n : ℤ) : ContDiff ℝ ∞ (heatMode k n) := by
  exact contDiff_const.mul ((heatModeLinear n).contDiff.cexp)

theorem heatMode_hasFDerivAt (k : ℕ) (n : ℤ) (p : ℝ × ℝ) :
    HasFDerivAt (heatMode k n) (heatMode k n p • heatModeLinear n) p := by
  have h := ((heatModeLinear n).hasFDerivAt (x := p)).cexp.const_mul ((n : ℂ) ^ k)
  convert! h using 1
  simp only [heatMode, smul_smul]

theorem heatMode_norm (k : ℕ) (n : ℤ) (p : ℝ × ℝ) :
    ‖heatMode k n p‖ = heatModeBound k p.1 n := by
  simp only [heatMode, norm_mul, norm_pow, Complex.norm_intCast,
    Complex.norm_exp, heatModeLinear_re, heatModeBound]

theorem heatModeBound_summable (k : ℕ) {T : ℝ} (hT : 0 < T) :
    Summable (heatModeBound k T) := by
  have h := summable_pow_mul_jacobiTheta₂_term_bound 0
    (T := 4 * Real.pi * T) (by positivity) k
  convert h using 1
  funext n
  simp only [heatModeBound, Int.cast_abs]
  congr 2
  ring

theorem heatMode_norm_le (k : ℕ) (n : ℤ) {T : ℝ} {p : ℝ × ℝ}
    (hp : T ≤ p.1) : ‖heatMode k n p‖ ≤ heatModeBound k T n := by
  rw [heatMode_norm]
  unfold heatModeBound
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonpos_left hp
  have h : 0 ≤ 4 * Real.pi ^ 2 * (n : ℝ) ^ 2 := by positivity
  linarith

theorem heatModeLinear_norm_le (n : ℤ) :
    ‖heatModeLinear n‖ ≤ 4 * Real.pi ^ 2 * |(n : ℝ)| ^ 2 + 2 * Real.pi * |(n : ℝ)| := by
  apply (heatModeLinear n).opNorm_le_bound (by positivity)
  intro p
  simp only [heatModeLinear, add_apply, smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', Complex.ofRealCLM_apply]
  calc
    _ ≤ ‖(-4 * Real.pi ^ 2 * (n : ℝ) ^ 2) • (p.1 : ℂ)‖ +
        ‖(2 * Real.pi * (n : ℝ)) • (Complex.I • (p.2 : ℂ))‖ := norm_add_le _ _
    _ = (4 * Real.pi ^ 2 * |(n : ℝ)| ^ 2) * |p.1| +
        (2 * Real.pi * |(n : ℝ)|) * |p.2| := by
      simp only [norm_smul, Real.norm_eq_abs, Complex.norm_real, Complex.norm_I,
        one_mul, abs_mul, abs_pow, abs_neg, abs_of_pos Real.pi_pos]
      norm_num
    _ ≤ _ := by
      have h₁ : |p.1| ≤ ‖p‖ := norm_fst_le p
      have h₂ : |p.2| ≤ ‖p‖ := norm_snd_le p
      nlinarith [mul_le_mul_of_nonneg_left h₁
          (show 0 ≤ 4 * Real.pi ^ 2 * |(n : ℝ)| ^ 2 by positivity),
        mul_le_mul_of_nonneg_left h₂
          (show 0 ≤ 2 * Real.pi * |(n : ℝ)| by positivity)]

def heatModeDerivativeBound (k : ℕ) (T : ℝ) (n : ℤ) : ℝ :=
  4 * Real.pi ^ 2 * heatModeBound (k + 2) T n +
    2 * Real.pi * heatModeBound (k + 1) T n

theorem heatModeDerivativeBound_summable (k : ℕ) {T : ℝ} (hT : 0 < T) :
    Summable (heatModeDerivativeBound k T) :=
  ((heatModeBound_summable (k + 2) hT).mul_left _).add
    ((heatModeBound_summable (k + 1) hT).mul_left _)

theorem heatMode_derivative_norm_le (k : ℕ) (n : ℤ) {T : ℝ} {p : ℝ × ℝ}
    (hp : T ≤ p.1) :
    ‖heatMode k n p • heatModeLinear n‖ ≤ heatModeDerivativeBound k T n := by
  rw [norm_smul]
  calc
    _ ≤ heatModeBound k T n *
        (4 * Real.pi ^ 2 * |(n : ℝ)| ^ 2 + 2 * Real.pi * |(n : ℝ)|) :=
      mul_le_mul (heatMode_norm_le k n hp) (heatModeLinear_norm_le n)
        (norm_nonneg _) (by unfold heatModeBound; positivity)
    _ = _ := by
      simp only [heatModeDerivativeBound, heatModeBound, pow_add]
      ring

end ForcedComputation.VelocityDetector

end

end OAI
