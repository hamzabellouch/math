import OAI.Probability.DilutedSpin.Core

namespace OAI

section
section
namespace DilutedSpinGlass
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

/-- Common Poisson points give the exact first-moment rate coupling estimate.
This is a consequence of convolution, not a coupling hypothesis. -/
theorem poisson_average_rate_add (r s : ℝ≥0) {f : ℕ → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (hstep : ∀ n, |f (n+1)-f n| ≤ C) :
    |(∫ n, f n ∂poissonMeasure (r+s))-(∫ n, f n ∂poissonMeasure r)| ≤ C*(s:ℝ) := by
  have hl := nat_lipschitz_of_step hC hstep
  have hb (n : ℕ) : |f n| ≤ |f 0|+C*n := by
    have hh := hl n 0
    simp only [Nat.cast_zero,sub_zero,abs_of_nonneg (Nat.cast_nonneg n : (0:ℝ) ≤ n)] at hh
    calc
      |f n| = |(f n-f 0)+f 0| := by congr 1; ring
      _ ≤ |f n-f 0|+|f 0| := abs_add_le _ _
      _ ≤ |f 0|+C*n := by linarith
  have hi (q : ℝ≥0) : Integrable f (poissonMeasure q) := poisson_integrable_linear q hb
  have hin (n : ℕ) : Integrable (fun k => f (n+k)) (poissonMeasure s) := by
    apply poisson_integrable_linear s (A := |f 0|+C*n) (B := C)
    intro k
    convert hb (n+k) using 1
    push_cast
    ring
  have hd (n : ℕ) : |(∫ k, f (n+k) ∂poissonMeasure s)-f n| ≤ C*(s:ℝ) := by
    have h := integral_mono ((hin n).sub (integrable_const (f n))).abs
      ((poisson_integrable_count s).const_mul C) (fun k => by
        change |f (n+k)-f n| ≤ C*(k:ℝ)
        have hh := hl (n+k) n
        simpa only [Nat.cast_add,add_sub_cancel_left,abs_of_nonneg (Nat.cast_nonneg k : (0:ℝ) ≤ k)] using hh)
    simp only [Pi.sub_apply] at h
    rw [integral_const_mul,poisson_mean] at h
    have ha := abs_integral_le_integral_abs.trans h
    rw [integral_sub (hin n) (integrable_const (f n))] at ha
    simpa only [integral_const,probReal_univ,smul_eq_mul,one_mul] using ha
  have hj : Integrable (fun n => ∫ k, f (n+k) ∂poissonMeasure s) (poissonMeasure r) := by
    apply poisson_integrable_linear r (A := |f 0|+C*s) (B := C)
    intro n
    have hh := abs_sub_le_iff.mp (hd n)
    have hf := abs_le.mp (hb n)
    rw [abs_le]
    constructor <;> linarith
  have hconv : Integrable f (poissonMeasure r ∗ poissonMeasure s) := by
    rw [poissonMeasure_conv_poissonMeasure]
    exact hi (r+s)
  rw [← poissonMeasure_conv_poissonMeasure,integral_conv hconv,← integral_sub hj (hi r)]
  exact abs_integral_le_bound hd

end DilutedSpinGlass
end

end

end OAI
