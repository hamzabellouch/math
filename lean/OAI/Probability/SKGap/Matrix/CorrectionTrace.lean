import Mathlib
import OAI.Probability.SKGap.Localization.Operation

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open Primary Matrix SKGap.SourceError
variable {n : ℕ}

lemma trace_frobenius (P E : Interaction n) : |trace (P*E)|≤‖P‖*‖E‖ := by
  have H := double_cauchy (fun i k=>P k i) (fun i k=>E i k)
    (norm_nonneg P) (norm_nonneg E)
    (by rw [Finset.sum_comm]; exact le_of_eq (SKGap.frobenius_sq P).symm)
    (le_of_eq (SKGap.frobenius_sq E).symm)
  rw [Matrix.trace_mul_comm]
  simpa only [trace,diag,Matrix.mul_apply,mul_comm] using H

lemma trace_small_diagonal (P E : Interaction n) (u : Fin n→ℝ) :
    |trace (P*(Matrix.diagonal u*E))|≤SKGap.opNorm P*vectorNorm u*‖E‖ := by
  apply (trace_le_traceAbsolute P (Matrix.diagonal u*E)).trans
  have H := double_cauchy (fun i k=>|P k i| *|u i|) (fun i k=>|E i k|)
    (mul_nonneg (real_op_norm_nonneg P) (vectorNorm_nonneg u)) (norm_nonneg E)
    (by simpa only [mul_pow,vectorNorm_sq] using small_column_square P u)
    (by simpa only [sq_abs] using le_of_eq (SKGap.frobenius_sq E).symm)
  have HH := (le_abs_self (∑i,∑k,(|P k i| * |u i|)*|E i k|)).trans H
  simpa only [traceAbsolute,Matrix.diagonal_mul,abs_mul,mul_assoc] using HH

lemma trace_small_mean (P E : Interaction n) (U : VectorFields n) (x : Spin n) (hn : 0<n) :
    |trace (P*(siteMean U x • E))|≤SKGap.opNorm P*vectorNorm (U x)*‖E‖ := by
  have hscaled := scaled_frobenius_by_rows P (siteMean U x) (vectorNorm_nonneg _) (real_op_norm_nonneg P)
    (siteMean_square U x hn) (matrix_row_square_le P)
  rw [Matrix.mul_smul,←Matrix.smul_mul]
  exact (trace_frobenius _ E).trans ((mul_le_mul_of_nonneg_right hscaled (norm_nonneg E)).trans_eq (by ring))

def averageError (a : Spin n→ℝ) (U : VectorFields n) (x : Spin n) : Interaction n :=
  derivativeMatrix (fun x i=>a x*U x i) x-a x • derivativeMatrix U x

lemma averageError_eq (a : Spin n→ℝ) (U : VectorFields n) (x : Spin n) :
    averageError a U x=Matrix.of (fun i k=>U x i*halfDiff k a x)-
      Matrix.of (fun i k=>2*spin x k*derivativeMatrix U x i k*halfDiff k a x) := by
  ext i k
  simp only [averageError,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,Matrix.of_apply,derivativeMatrix]
  rw [halfDiff_mul]
  ring

lemma trace_column_scaled (P D : Interaction n) (t : Fin n→ℝ) (x : Spin n) :
    |trace (P*Matrix.of (fun i k=>2*spin x k*D i k*t k))|≤
      2*‖D‖*(SKGap.opNorm P*vectorNorm t) := by
  apply (trace_le_traceAbsolute P _).trans
  have H:=parameter_product_trace_bound P D t (norm_nonneg D) (vectorNorm_nonneg t)
    (le_of_eq (SKGap.frobenius_sq D).symm) (le_of_eq (vectorNorm_sq t).symm)
  have he : traceAbsolute P (Matrix.of (fun i k=>2*spin x k*D i k*t k))=
      2*(∑i,∑k,|P k i| *|D i k| *|t k|) := by
    simp only [traceAbsolute,Matrix.of_apply,abs_mul,abs_spin_eq_one,mul_one,
      abs_of_pos (by norm_num : (0:ℝ)<2),Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro k _; ring
  rw [he]
  exact (mul_le_mul_of_nonneg_left H (by norm_num)).trans_eq (by ring)

lemma averageError_trace (P : Interaction n) (a : Spin n→ℝ) (U : VectorFields n) (x : Spin n) :
    |trace (P*averageError a U x)|≤
      SKGap.opNorm P*(vectorNorm (U x)+2*‖derivativeMatrix U x‖)*‖derivativeVector a x‖ := by
  rw [averageError_eq,mul_sub,trace_sub]
  have h₁:=rank_one_trace_bound P (WithLp.toLp 2 (U x)) (derivativeVector a x)
  have h₂:=trace_column_scaled P (derivativeMatrix U x) (fun k=>halfDiff k a x) x
  apply ((abs_sub _ _).trans (add_le_add h₁ h₂)).trans_eq
  change SKGap.opNorm P*vectorNorm (U x)*‖derivativeVector a x‖+
    2*‖derivativeMatrix U x‖*(SKGap.opNorm P*‖derivativeVector a x‖)=_
  ring

lemma primary_averageError_trace (P : Interaction n) (U m : VectorFields n) (x : Spin n) (hn : 0<n)
    {C R : ℝ} (hC : 0≤C) (hR : 0≤R) (hU : ‖derivativeMatrix U x‖≤C)
    (hm : ∀i,|m x i|≤1) (hdm : SKGap.opNorm (derivativeMatrix m x)≤R) :
    |trace (P*averageError (siteMean U) m x)|≤SKGap.opNorm P*C*(1+2*R) := by
  have hd : (n:ℝ)*‖derivativeVector (siteMean U) x‖^2≤C^2 :=
    siteMean_derivative_square_bound hn ((opNorm_le_frobenius _).trans hU)
  have hm2 : vectorNorm (m x)^2≤(n:ℝ) := by
    rw [vectorNorm_sq]
    calc
      _ ≤ ∑_i:Fin n,(1:ℝ) := Finset.sum_le_sum fun i _=>by nlinarith [hm i,sq_abs (m x i),abs_nonneg (m x i)]
      _ = _ := by simp
  have hdm2 : ‖derivativeMatrix m x‖^2≤(n:ℝ)*R^2 := by
    rw [SKGap.frobenius_sq]
    calc
      _ ≤ ∑_i:Fin n,R^2 := Finset.sum_le_sum fun i _=>
        (matrix_row_square_le _ i).trans (pow_le_pow_left₀ (real_op_norm_nonneg _) hdm 2)
      _ = _ := by simp
  have h₁ : vectorNorm (m x)*‖derivativeVector (siteMean U) x‖≤C := by
    apply nonneg_le_nonneg_of_sq_le_sq hC
    simp only [←sq,mul_pow]
    exact (mul_le_mul_of_nonneg_right hm2 (sq_nonneg _)).trans hd
  have h₂ : ‖derivativeMatrix m x‖*‖derivativeVector (siteMean U) x‖≤C*R := by
    apply nonneg_le_nonneg_of_sq_le_sq (mul_nonneg hC hR)
    simp only [←sq,mul_pow]
    have H := (mul_le_mul_of_nonneg_right hdm2 (sq_nonneg ‖derivativeVector (siteMean U) x‖)).trans
      (show (n:ℝ)*R^2*‖derivativeVector (siteMean U) x‖^2≤C^2*R^2 by
        nlinarith [mul_le_mul_of_nonneg_right hd (sq_nonneg R)])
    exact H
  apply (averageError_trace P (siteMean U) m x).trans
  have H := mul_le_mul_of_nonneg_left (add_le_add h₁ (mul_le_mul_of_nonneg_left h₂ (by norm_num : (0:ℝ)≤2)))
    (real_op_norm_nonneg P)
  nlinarith only [H]

end SKGapCutoff.Recipe

end
end

end OAI
