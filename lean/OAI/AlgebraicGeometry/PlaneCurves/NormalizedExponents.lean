import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Tactic.FieldSimp
import OAI.AlgebraicGeometry.PlaneCurves.ThetaExponents

namespace OAI

/-!
# Normalized exponent intervals for automorphic sections
-/

section

/-! Exact exponential algebra and deck periods of the source normalized theta summands. -/
noncomputable section
namespace Nagata.W08
open Nagata.W07

/-- The upper-half-plane period parameter corresponding to the real nome `τ`. -/
def thetaJacobiParameter (n τ : ℝ) : ℂ :=
  ((n * Real.log τ : ℝ) : ℂ) / (2 * (Real.pi : ℂ) * Complex.I)

/-- The affine first argument of Jacobi theta for the source normalized series. -/
def thetaJacobiArgument (n a : ℝ) (ε : ℂ) (τ : ℝ) (x : ℂ) : ℂ :=
  ((n : ℂ) * x + (((a - n / 2) * Real.log τ : ℝ) : ℂ) - Complex.log ε) /
    (2 * (Real.pi : ℂ) * Complex.I)

/-- Exact equality of actual summands, retaining every scalar normalization. -/
theorem normalizedThetaTerm_eq_exponential (n a K : ℝ) {ε : ℂ} (hε : ε ≠ 0)
    {τ : ℝ} (hτ : 0 < τ) (p : ℤ) (x : ℂ) :
    normalizedThetaTerm n a K ε τ p x =
      Complex.exp ((K : ℂ) * x) *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (p : ℂ) * thetaJacobiArgument n a ε τ x +
          (Real.pi : ℂ) * Complex.I * (p : ℂ) ^ 2 * thetaJacobiParameter n τ) := by
  have heps : ε ^ (-p) = Complex.exp (((-p : ℤ) : ℂ) * Complex.log ε) := by
    rw [Complex.exp_int_mul, Complex.exp_log hε]
  unfold normalizedThetaTerm
  rw [heps, Real.rpow_def_of_pos hτ, Complex.ofReal_exp,
    ← Complex.exp_add, ← Complex.exp_add]
  unfold thetaJacobiArgument thetaJacobiParameter
  rw [← Complex.exp_add]
  congr 1
  unfold thetaExponent
  push_cast
  field_simp [Complex.I_ne_zero,
    show (Real.pi : ℂ) ≠ 0 from Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
  ring

/-- The Jacobi parameter lies in the genuine convergence domain. -/
theorem thetaJacobiParameter_im_pos {n τ : ℝ}
    (hn : 0 < n) (hτ : 0 < τ) (hτone : τ < 1) :
    0 < (thetaJacobiParameter n τ).im := by
  have hnlog : n * Real.log τ < 0 := mul_neg_of_pos_of_neg hn (Real.log_neg hτ hτone)
  have htwoPi : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have hden : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero
  have hdenpos := Complex.normSq_pos.mpr hden
  have hquot : n * Real.log τ * (2 * Real.pi) /
      Complex.normSq (2 * (Real.pi : ℂ) * Complex.I) < 0 :=
    div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hnlog htwoPi) hdenpos
  simpa [thetaJacobiParameter, Complex.div_im, Complex.mul_re, Complex.mul_im] using
    neg_pos.mpr hquot

/-- Integer-frequency summands are independent of the logarithm branch. -/
theorem normalizedThetaTerm_integerPeriod (n K k : ℤ) (a : ℝ) (ε : ℂ) (τ : ℝ)
    (p : ℤ) (x : ℂ) :
    normalizedThetaTerm (n : ℝ) a (K : ℝ) ε τ p
        (x + (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) =
      normalizedThetaTerm (n : ℝ) a (K : ℝ) ε τ p x := by
  have hfreq : (((K : ℝ) + (n : ℝ) * (p : ℝ) : ℝ) : ℂ) =
      ((K + n * p : ℤ) : ℂ) := by push_cast; rfl
  unfold normalizedThetaTerm
  rw [hfreq, mul_add, Complex.exp_add]
  have hexp : Complex.exp (((K + n * p : ℤ) : ℂ) *
      ((k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I))) = 1 := by
    rw [← mul_assoc, ← Int.cast_mul]
    exact Complex.exp_int_mul_two_pi_mul_I ((K + n * p) * k)
  rw [hexp, mul_one]

/-- Branch independence of the actual `tsum`, without any hidden convergence hypothesis. -/
theorem normalizedThetaSeries_integerPeriod (n K k : ℤ) (a : ℝ) (ε : ℂ) (τ : ℝ)
    (x : ℂ) :
    (∑' p : ℤ, normalizedThetaTerm (n : ℝ) a (K : ℝ) ε τ p
      (x + (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I))) =
    (∑' p : ℤ, normalizedThetaTerm (n : ℝ) a (K : ℝ) ε τ p x) :=
  tsum_congr fun p ↦ normalizedThetaTerm_integerPeriod n K k a ε τ p x

/-- The literal normalized summand as one complex exponential. -/
theorem normalizedThetaTerm_eq_singleExp (n a K : ℝ) {ε : ℂ} (hε : ε ≠ 0)
    {τ : ℝ} (hτ : 0 < τ) (p : ℤ) (x : ℂ) :
    normalizedThetaTerm n a K ε τ p x =
      Complex.exp (((-p : ℤ) : ℂ) * Complex.log ε +
        ((Real.log τ * thetaExponent n a (p : ℝ) : ℝ) : ℂ) +
        (((K + n * (p : ℝ) : ℝ) : ℂ) * x)) := by
  have heps : ε ^ (-p) = Complex.exp (((-p : ℤ) : ℂ) * Complex.log ε) := by
    rw [Complex.exp_int_mul, Complex.exp_log hε]
  unfold normalizedThetaTerm
  rw [heps, Real.rpow_def_of_pos hτ, Complex.ofReal_exp,
    ← Complex.exp_add, ← Complex.exp_add]

/-- One scalar shift agrees exactly with one integer reindexing of actual summands. -/
theorem normalizedThetaTerm_realShift_index (n a K : ℝ) {ε : ℂ} (hε : ε ≠ 0)
    {τ : ℝ} (hτ : 0 < τ) (p : ℤ) (x : ℂ) :
    normalizedThetaTerm n a K ε τ p (x + (Real.log τ : ℂ)) =
      ((ε * ((τ ^ (K - a) : ℝ) : ℂ)) * Complex.exp (-(n : ℂ) * x)) *
        normalizedThetaTerm n a K ε τ (p + 1) x := by
  have hscalar : ε * ((τ ^ (K - a) : ℝ) : ℂ) =
      Complex.exp (Complex.log ε + ((Real.log τ * (K - a) : ℝ) : ℂ)) := by
    rw [Complex.exp_add, Complex.exp_log hε, Real.rpow_def_of_pos hτ, Complex.ofReal_exp]
  rw [normalizedThetaTerm_eq_singleExp n a K hε hτ,
    normalizedThetaTerm_eq_singleExp n a K hε hτ, hscalar,
    ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  unfold thetaExponent
  push_cast
  ring

/-- The exact additive multiplier law, proved by integer reindexing without Jacobi theta. -/
theorem normalizedThetaSeries_realShift (n a K : ℝ) {ε : ℂ} (hε : ε ≠ 0)
    {τ : ℝ} (hτ : 0 < τ) (x : ℂ) :
    (∑' p : ℤ, normalizedThetaTerm n a K ε τ p (x + (Real.log τ : ℂ))) =
      (ε * ((τ ^ (K - a) : ℝ) : ℂ)) * Complex.exp (-(n : ℂ) * x) *
        (∑' p : ℤ, normalizedThetaTerm n a K ε τ p x) := by
  simp_rw [normalizedThetaTerm_realShift_index n a K hε hτ]
  rw [tsum_mul_left]
  congr 1
  exact (Equiv.addRight (1 : ℤ)).tsum_eq (fun p : ℤ ↦ normalizedThetaTerm n a K ε τ p x)

end Nagata.W08

end
end

end OAI
