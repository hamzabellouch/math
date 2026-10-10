import Mathlib

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

/- Literal invariant tube measure coefficient with respect to `ds dω`. -/
def tubeMeasureCoefficient (n : ℕ) (h B Q : ℝ) : ℝ :=
  h ^ (-(n : ℝ)/2) * Real.sqrt (B*Q)

lemma tubeMeasureCoefficient_pos {n : ℕ} {h B Q : ℝ}
    (hh : 0 < h) (hB : 0 < B) (hQ : 0 < Q) :
    0 < tubeMeasureCoefficient n h B Q :=
  mul_pos (Real.rpow_pos_of_pos hh _) (Real.sqrt_pos.2 (mul_pos hB hQ))

lemma tubeMeasureCoefficient_base {n : ℕ} {h B Q : ℝ}
    (hh : 0 < h) (hB : 0 < B) (hQ : 0 < Q) :
    tubeMeasureCoefficient n h B Q*h/B =
      Real.exp (-(n : ℝ)*Real.log h - (((n : ℝ)+2)/2)*
        ((Real.log B-Real.log Q)/((n : ℝ)+2)-Real.log h)) := by
  have hN : (n : ℝ)+2 ≠ 0 := by positivity
  have hl : 0 < tubeMeasureCoefficient n h B Q*h/B :=
    div_pos (mul_pos (tubeMeasureCoefficient_pos hh hB hQ) hh) hB
  rw [← Real.exp_log hl]
  congr 1
  rw [Real.log_div (mul_ne_zero (tubeMeasureCoefficient_pos hh hB hQ).ne' hh.ne') hB.ne',
    Real.log_mul (tubeMeasureCoefficient_pos hh hB hQ).ne' hh.ne']
  unfold tubeMeasureCoefficient
  rw [Real.log_mul (Real.rpow_pos_of_pos hh _).ne' (Real.sqrt_pos.2 (mul_pos hB hQ)).ne',
    Real.log_rpow hh,Real.log_sqrt (mul_pos hB hQ).le,Real.log_mul hB.ne' hQ.ne']
  field_simp
  ring

lemma tubeMeasureCoefficient_angular {n : ℕ} {h B Q : ℝ}
    (hh : 0 < h) (hB : 0 < B) (hQ : 0 < Q) :
    tubeMeasureCoefficient n h B Q*h/Q =
      Real.exp (2*Real.log h + (((n : ℝ)+2)/2)*
        ((Real.log B-Real.log Q)/((n : ℝ)+2)-Real.log h)) := by
  have hN : (n : ℝ)+2 ≠ 0 := by positivity
  have hl : 0 < tubeMeasureCoefficient n h B Q*h/Q :=
    div_pos (mul_pos (tubeMeasureCoefficient_pos hh hB hQ) hh) hQ
  rw [← Real.exp_log hl]
  congr 1
  rw [Real.log_div (mul_ne_zero (tubeMeasureCoefficient_pos hh hB hQ).ne' hh.ne') hQ.ne',
    Real.log_mul (tubeMeasureCoefficient_pos hh hB hQ).ne' hh.ne']
  unfold tubeMeasureCoefficient
  rw [Real.log_mul (Real.rpow_pos_of_pos hh _).ne' (Real.sqrt_pos.2 (mul_pos hB hQ)).ne',
    Real.log_rpow hh,Real.log_sqrt (mul_pos hB hQ).le,Real.log_mul hB.ne' hQ.ne']
  field_simp
  ring

end AffineBernstein
end

end OAI
