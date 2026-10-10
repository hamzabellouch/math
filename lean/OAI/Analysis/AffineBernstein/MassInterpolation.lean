import Mathlib
import OAI.Analysis.AffineBernstein.TubeWeightAlgebra

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

lemma tube_area_factorization {n : ℕ} {h B Q : ℝ}
    (hh : 0 < h) (hB : 0 < B) (hQ : 0 < Q) :
    B ^ (1/((n:ℝ)+2)) * Q ^ (1-1/((n:ℝ)+2)) =
      (tubeMeasureCoefficient n h B Q)^(2/((n:ℝ)+2)) *
        h ^ ((n:ℝ)/((n:ℝ)+2)) * Q ^ (1-2/((n:ℝ)+2)) := by
  have hN : (n:ℝ)+2 ≠ 0 := by positivity
  have hμ := tubeMeasureCoefficient_pos (n := n) hh hB hQ
  apply Real.log_injOn_pos
  · change (0:ℝ) < _
    positivity
  · change (0:ℝ) < _
    positivity
  rw [Real.log_mul (Real.rpow_pos_of_pos hB _).ne' (Real.rpow_pos_of_pos hQ _).ne',
    Real.log_rpow hB,Real.log_rpow hQ,
    Real.log_mul (mul_pos (Real.rpow_pos_of_pos hμ _) (Real.rpow_pos_of_pos hh _)).ne'
      (Real.rpow_pos_of_pos hQ _).ne',
    Real.log_mul (Real.rpow_pos_of_pos hμ _).ne' (Real.rpow_pos_of_pos hh _).ne',
    Real.log_rpow hμ,Real.log_rpow hh,Real.log_rpow hQ]
  unfold tubeMeasureCoefficient
  rw [Real.log_mul (Real.rpow_pos_of_pos hh _).ne' (Real.sqrt_pos.2 (mul_pos hB hQ)).ne',
    Real.log_rpow hh,Real.log_sqrt (mul_pos hB hQ).le,Real.log_mul hB.ne' hQ.ne']
  field_simp
  ring

lemma weighted_tube_interpolation {n : ℕ} {B Q t : ℝ}
    (hB : 0 < B) (hQ : 0 < Q) (ht : 0 < t) :
    Real.sqrt (B*Q)*t =
      (B ^ (1/((n:ℝ)+2)) * Q ^ (1-1/((n:ℝ)+2))*t) ^
        (((n:ℝ)+2)/(2*((n:ℝ)+1))) *
      (B*t) ^ (1-((n:ℝ)+2)/(2*((n:ℝ)+1))) := by
  have hN : (n:ℝ)+2 ≠ 0 := by positivity
  have hP : (n:ℝ)+1 ≠ 0 := by positivity
  have hI : 0 < B ^ (1/((n:ℝ)+2)) * Q ^ (1-1/((n:ℝ)+2)) := by positivity
  apply Real.log_injOn_pos
  · change (0:ℝ) < _
    positivity
  · change (0:ℝ) < _
    positivity
  rw [Real.log_mul (Real.sqrt_pos.2 (mul_pos hB hQ)).ne' ht.ne',
    Real.log_sqrt (mul_pos hB hQ).le,Real.log_mul hB.ne' hQ.ne',
    Real.log_mul (Real.rpow_pos_of_pos (mul_pos hI ht) _).ne'
      (Real.rpow_pos_of_pos (mul_pos hB ht) _).ne',
    Real.log_rpow (mul_pos hI ht),Real.log_rpow (mul_pos hB ht),
    Real.log_mul hI.ne' ht.ne',Real.log_mul hB.ne' ht.ne',
    Real.log_mul (Real.rpow_pos_of_pos hB _).ne' (Real.rpow_pos_of_pos hQ _).ne',
    Real.log_rpow hB,Real.log_rpow hQ]
  field_simp
  ring

lemma weighted_tube_exponent {n : ℕ} (hn : 1 ≤ n) :
    0 < ((n:ℝ)+2)/(2*((n:ℝ)+1)) ∧ ((n:ℝ)+2)/(2*((n:ℝ)+1)) < 1 := by
  have h : (1:ℝ) ≤ n := by exact_mod_cast hn
  constructor
  · positivity
  · apply (div_lt_one (by positivity)).2
    linarith

end AffineBernstein
end

end OAI
