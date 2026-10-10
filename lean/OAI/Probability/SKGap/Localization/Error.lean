import Mathlib
import OAI.Probability.SKGap.Localization.Bilinear
import OAI.Probability.SKGap.Matrix.MatrixSeminorm

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGap.SourceError
open Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local instance : Fact (1≤(4:ENNReal)) := ⟨by norm_num⟩

lemma real_op_norm_nonneg (P : Matrix ι ι ℝ) : 0≤opNorm P := norm_nonneg _

lemma cauchy_bound {α : Type*} [Fintype α] (f g : α→ℝ) {A B : ℝ}
    (hA : 0≤A) (hB : 0≤B) (hf : (∑i,(f i)^2)≤A^2) (hg : (∑i,(g i)^2)≤B^2) :
    |∑i,f i*g i|≤A*B := by
  have H:=Finset.sum_mul_sq_le_sq_mul_sq Finset.univ f g
  have hh:=mul_le_mul hf hg (Finset.sum_nonneg (fun i _=>sq_nonneg _)) (sq_nonneg _)
  nlinarith [sq_abs (∑i,f i*g i),mul_nonneg hA hB,abs_nonneg (∑i,f i*g i)]

omit [DecidableEq ι] in
lemma double_cauchy (f g : ι→ι→ℝ) {A B : ℝ} (hA : 0≤A) (hB : 0≤B)
    (hf : (∑i,∑k,(f i k)^2)≤A^2) (hg : (∑i,∑k,(g i k)^2)≤B^2) :
    |∑i,∑k,f i k*g i k|≤A*B := by
  have H:=cauchy_bound (fun a : ι×ι=>f a.1 a.2) (fun a=>g a.1 a.2) hA hB
    (by simpa only [Fintype.sum_prod_type] using hf) (by simpa only [Fintype.sum_prod_type] using hg)
  simpa only [Fintype.sum_prod_type] using H

def traceAbsolute (P E : Matrix ι ι ℝ) : ℝ := ∑i,∑k,|P k i| * |E i k|

omit [DecidableEq ι] in
lemma trace_le_traceAbsolute (P E : Matrix ι ι ℝ) : |trace (P*E)|≤traceAbsolute P E := by
  rw [trace_mul_comm]
  simp only [trace,diag,Matrix.mul_apply]
  apply (Finset.abs_sum_le_sum_abs ..).trans
  apply Finset.sum_le_sum; intro i _
  exact (Finset.abs_sum_le_sum_abs ..).trans_eq (by simp only [abs_mul,mul_comm])

lemma matrix_column_square_le (P : Matrix ι ι ℝ) (i : ι) :
    (∑k,(P k i)^2)≤(opNorm P)^2 := by
  have H:=pow_le_pow_left₀ (norm_nonneg (colVec P i)) (colVec_norm_le P i) 2
  simpa only [colVec,EuclideanSpace.real_norm_sq_eq] using H

lemma matrix_row_square_le (P : Matrix ι ι ℝ) (i : ι) :
    (∑k,(P i k)^2)≤(opNorm P)^2 := by
  simpa only [Matrix.transpose_apply,opNorm_transpose] using matrix_column_square_le Pᵀ i

lemma small_column_square (P : Matrix ι ι ℝ) (s : ι→ℝ) :
    (∑i,∑k,(|P k i| * |s i|)^2)≤(opNorm P)^2*(∑i,(s i)^2) := by
  simp only [mul_pow,sq_abs]
  calc
    _ ≤ ∑i,(opNorm P)^2*(s i)^2 := by
      apply Finset.sum_le_sum; intro i _
      rw [←Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right (matrix_column_square_le P i) (sq_nonneg _)
    _ = _ := by rw [←Finset.mul_sum]

lemma small_row_square (P : Matrix ι ι ℝ) (t : ι→ℝ) :
    (∑i,∑k,(|P k i| * |t k|)^2)≤(opNorm P)^2*(∑k,(t k)^2) := by
  rw [Finset.sum_comm]
  simpa only [Matrix.transpose_apply,opNorm_transpose] using small_column_square Pᵀ t

lemma quadratic_trace_bound (P Q : Matrix ι ι ℝ) (s : ι→ℝ) {S B : ℝ}
    (hS : 0≤S) (hB : 0≤B) (hs : (∑i,(s i)^2)≤S^2)
    (hQ : (∑i,∑k,(Q i k)^4)≤B^4) :
    (∑i,∑k,|P k i| * |s i| *(Q i k)^2)≤opNorm P*S*B^2 := by
  have H:=double_cauchy (fun i k=>|P k i| * |s i|) (fun i k=>(Q i k)^2)
    (mul_nonneg (real_op_norm_nonneg P) hS) (pow_nonneg hB 2)
    ((small_column_square P s).trans (by
      simpa only [mul_pow] using mul_le_mul_of_nonneg_left hs (sq_nonneg (opNorm P))))
    (by simpa only [←pow_mul] using hQ)
  exact (le_abs_self _).trans H

lemma mixed_trace_bound (P Q : Matrix ι ι ℝ) (s t : ι→ℝ) {S T B : ℝ}
    (hS : 0≤S) (hT : 0≤T) (hB : 0≤B)
    (hs : (∑i,(s i)^2)≤S^2) (ht : (∑k,(t k)^2)≤T^2)
    (hQ : ∀i,(∑k,(Q i k)^2)≤B^2) :
    (∑i,∑k,|P k i| * |s i| * |Q i k| * |t k|)≤opNorm P*T*(S*B) := by
  have hf : (∑i,∑k,(|P k i| * |t k|)^2)≤(opNorm P*T)^2 :=
    (small_row_square P t).trans (by simpa only [mul_pow] using (mul_le_mul_of_nonneg_left ht (sq_nonneg (opNorm P))))
  have hg : (∑i,∑k,(|s i| * |Q i k|)^2)≤(S*B)^2 := by
    simp only [mul_pow,sq_abs,←Finset.mul_sum]
    calc
      _ ≤ ∑i,(s i)^2*B^2 := Finset.sum_le_sum (fun i _=>mul_le_mul_of_nonneg_left (hQ i) (sq_nonneg _))
      _ = (∑i,(s i)^2)*B^2 := (Finset.sum_mul ..).symm
      _ ≤ S^2*B^2 := mul_le_mul_of_nonneg_right hs (sq_nonneg _)
  have H:=double_cauchy (fun i k=>|P k i| * |t k|) (fun i k=>|s i| * |Q i k|)
    (mul_nonneg (real_op_norm_nonneg P) hT) (mul_nonneg hS hB) hf hg
  apply (le_abs_self _).trans
  have he : (∑i,∑k,|P k i| * |s i| * |Q i k| * |t k|) =
      ∑i,∑k,|P k i| * |t k| * (|s i| * |Q i k|) := by
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro k _; ring
  rw [he]
  exact H

lemma parameter_square_trace_bound (P : Matrix ι ι ℝ) (s t : ι→ℝ) {S T : ℝ}
    (hS : 0≤S) (hT : 0≤T) (hs : (∑i,(s i)^2)≤S^2) (ht : (∑k,(t k)^2)≤T^2) :
    (∑i,∑k,|P k i| * |s i| *(t k)^2)≤opNorm P*T*(S*T) := by
  have hf : (∑i,∑k,(|P k i| * |t k|)^2)≤(opNorm P*T)^2 :=
    (small_row_square P t).trans (by simpa only [mul_pow] using (mul_le_mul_of_nonneg_left ht (sq_nonneg (opNorm P))))
  have hg : (∑i,∑k,(|s i| * |t k|)^2)≤(S*T)^2 := by
    simp only [mul_pow,sq_abs,←Finset.mul_sum,←Finset.sum_mul]
    exact mul_le_mul hs ht (Finset.sum_nonneg (fun k _=>sq_nonneg _)) (sq_nonneg _)
  have H:=double_cauchy (fun i k=>|P k i| * |t k|) (fun i k=>|s i| * |t k|)
    (mul_nonneg (real_op_norm_nonneg P) hT) (mul_nonneg hS hT) hf hg
  apply (le_abs_self _).trans
  have he : (∑i,∑k,|P k i| * |s i| * (t k)^2) =
      ∑i,∑k,|P k i| * |t k| * (|s i| * |t k|) := by
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro k _
    rw [← sq_abs (t k)]; ring
  rw [he]
  exact H

theorem source_taylor_trace_bound (P E Q : Matrix ι ι ℝ) (s t : ι→ℝ) {C S T B R : ℝ}
    (hC : 0≤C) (hS : 0≤S) (hT : 0≤T) (hB : 0≤B) (hR : 0≤R)
    (hs : (∑i,(s i)^2)≤S^2) (ht : (∑k,(t k)^2)≤T^2)
    (hQ4 : (∑i,∑k,(Q i k)^4)≤B^4) (hQr : ∀i,(∑k,(Q i k)^2)≤R^2)
    (hE : ∀i k,|E i k|≤C*|s i| *((Q i k)^2+|Q i k| * |t k|+(t k)^2)) :
    |trace (P*E)|≤C*opNorm P*S*(B^2+R*T+T^2) := by
  apply (trace_le_traceAbsolute P E).trans
  calc
    _ ≤ ∑i,∑k,|P k i| *(C*|s i| *((Q i k)^2+|Q i k| * |t k|+(t k)^2)) := by
      apply Finset.sum_le_sum; intro i _
      apply Finset.sum_le_sum; intro k _
      exact mul_le_mul_of_nonneg_left (hE i k) (abs_nonneg _)
    _ = C*((∑i,∑k,|P k i| * |s i| *(Q i k)^2)+
      (∑i,∑k,|P k i| * |s i| * |Q i k| * |t k|)+
      (∑i,∑k,|P k i| * |s i| *(t k)^2)) := by
      simp only [Finset.mul_sum,←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro k _; ring
    _ ≤ C*(opNorm P*S*B^2+opNorm P*T*(S*R)+opNorm P*T*(S*T)) := by
      exact mul_le_mul_of_nonneg_left (add_le_add (add_le_add
        (quadratic_trace_bound P Q s hS hB hs hQ4)
        (mixed_trace_bound P Q s t hS hT hR hs ht hQr))
        (parameter_square_trace_bound P s t hS hT hs ht)) hC
    _ = _ := by ring

omit [DecidableEq ι] in
lemma fourth_holder (P D Q : Matrix ι ι ℝ) {B S R : ℝ}
    (hB : 0≤B) (hS : 0≤S) (hR : 0≤R)
    (hP : (∑i,∑k,(P i k)^4)≤B^4) (hD : (∑i,∑k,(D i k)^2)≤S^2)
    (hQ : (∑i,∑k,(Q i k)^4)≤R^4) :
    (∑i,∑k,|P i k| * |D i k| * |Q i k|)≤S*(B*R) := by
  have H₁:=double_cauchy (fun i k=>(P i k)^2) (fun i k=>(Q i k)^2)
    (sq_nonneg B) (sq_nonneg R) (by simpa only [←pow_mul] using hP)
    (by simpa only [←pow_mul] using hQ)
  have H₂ : (∑i,∑k,(|P i k| * |Q i k|)^2)≤(B*R)^2 := by
    simp only [mul_pow,sq_abs]
    exact (le_abs_self _).trans H₁
  have H₃:=double_cauchy (fun i k=>|D i k|) (fun i k=>|P i k| * |Q i k|)
    hS (mul_nonneg hB hR) (by simpa only [sq_abs] using hD) H₂
  apply (le_abs_self _).trans
  have he : (∑i,∑k,|P i k| * |D i k| * |Q i k|) =
      ∑i,∑k,|D i k| * (|P i k| * |Q i k|) := by
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro k _; ring
  rw [he]; exact H₃

lemma sum_split_diagonal (f : ι→ι→ℝ) :
    (∑i,∑k,f i k)=(∑i,f i i)+(∑i,∑k,if i=k then 0 else f i k) := by
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro i _
  have he : f i i=∑k,if i=k then f i k else 0 := by simp
  rw [he,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro k _
  split_ifs <;> simp

lemma diagonal_product_trace_bound (P D Q : Matrix ι ι ℝ) {S R : ℝ}
    (hS : 0≤S) (hR : 0≤R) (hD : (∑i,(D i i)^2)≤S^2)
    (hQ : (∑i,(Q i i)^2)≤R^2) :
    (∑i,|P i i| * |D i i| * |Q i i|)≤opNorm P*(S*R) := by
  calc
    _ ≤ ∑i,opNorm P*(|D i i| * |Q i i|) := by
      apply Finset.sum_le_sum; intro i _
      nlinarith [mul_le_mul_of_nonneg_right (matrix_entry_le_opNorm P i i)
        (mul_nonneg (abs_nonneg (D i i)) (abs_nonneg (Q i i)))]
    _ = opNorm P*(∑i,|D i i| * |Q i i|) := by rw [Finset.mul_sum]
    _ ≤ opNorm P*(S*R) := by
      apply mul_le_mul_of_nonneg_left _ (real_op_norm_nonneg P)
      exact (le_abs_self _).trans (cauchy_bound (fun i=>|D i i|) (fun i=>|Q i i|)
        hS hR (by simpa only [sq_abs] using hD) (by simpa only [sq_abs] using hQ))

lemma parameter_product_trace_bound (P D : Matrix ι ι ℝ) (t : ι→ℝ) {S T : ℝ}
    (hS : 0≤S) (hT : 0≤T) (hD : (∑i,∑k,(D i k)^2)≤S^2)
    (ht : (∑k,(t k)^2)≤T^2) :
    (∑i,∑k,|P k i| * |D i k| * |t k|)≤S*(opNorm P*T) := by
  have hf : (∑i,∑k,(|P k i| * |t k|)^2)≤(opNorm P*T)^2 :=
    (small_row_square P t).trans (by simpa only [mul_pow] using
      (mul_le_mul_of_nonneg_left ht (sq_nonneg (opNorm P))))
  have H:=double_cauchy (fun i k=>|D i k|) (fun i k=>|P k i| * |t k|)
    hS (mul_nonneg (real_op_norm_nonneg P) hT) (by simpa only [sq_abs] using hD) hf
  apply (le_abs_self _).trans
  have he : (∑i,∑k,|P k i| * |D i k| * |t k|) =
      ∑i,∑k,|D i k| * (|P k i| * |t k|) := by
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro k _; ring
  rw [he]; exact H

theorem source_product_trace_bound (P E D Q : Matrix ι ι ℝ) (t : ι→ℝ) {C S T B R L : ℝ}
    (hC : 0≤C) (hS : 0≤S) (hT : 0≤T) (hB : 0≤B) (hR : 0≤R) (hL : 0≤L)
    (hD : (∑i,∑k,(D i k)^2)≤S^2) (ht : (∑k,(t k)^2)≤T^2)
    (hP : (∑i,∑k,if i=k then 0 else (P k i)^4)≤B^4)
    (hQ : (∑i,∑k,(Q i k)^4)≤R^4) (hQd : (∑i,(Q i i)^2)≤L^2)
    (hE : ∀i k,|E i k|≤C*|D i k| *(|Q i k|+|t k|)) :
    |trace (P*E)|≤C*S*(B*R+opNorm P*(L+T)) := by
  have hDd : (∑i,(D i i)^2)≤S^2 := by
    apply le_trans _ hD
    exact Finset.sum_le_sum (fun i _=>Finset.single_le_sum (fun k _=>sq_nonneg (D i k))
      (Finset.mem_univ i))
  let O : Matrix ι ι ℝ := fun i k=>if i=k then 0 else P k i
  have hO : (∑i,∑k,(O i k)^4)≤B^4 := by
    simpa only [O,ite_pow,zero_pow (by decide : 4≠0)] using hP
  have hOff := fourth_holder O D Q hB hS hR hO hD hQ
  have heOff : (∑i,∑k,if i=k then 0 else |P k i| * |D i k| * |Q i k|) =
      ∑i,∑k,|O i k| * |D i k| * |Q i k| := by
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro k _
    dsimp only [O]; split_ifs <;> simp
  have hProd : (∑i,∑k,|P k i| * |D i k| * |Q i k|)≤opNorm P*(S*L)+S*(B*R) := by
    rw [sum_split_diagonal,heOff]
    exact add_le_add (diagonal_product_trace_bound P D Q hS hL hDd hQd) hOff
  apply (trace_le_traceAbsolute P E).trans
  calc
    _ ≤ ∑i,∑k,|P k i| *(C*|D i k| *(|Q i k|+|t k|)) := by
      apply Finset.sum_le_sum; intro i _
      apply Finset.sum_le_sum; intro k _
      exact mul_le_mul_of_nonneg_left (hE i k) (abs_nonneg _)
    _ = C*((∑i,∑k,|P k i| * |D i k| * |Q i k|)+
        (∑i,∑k,|P k i| * |D i k| * |t k|)) := by
      simp only [Finset.mul_sum,←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro k _; ring
    _ ≤ C*(opNorm P*(S*L)+S*(B*R)+S*(opNorm P*T)) :=
      mul_le_mul_of_nonneg_left (add_le_add hProd
        (parameter_product_trace_bound P D t hS hT hD ht)) hC
    _ = _ := by ring

lemma trace_square_eq (E : Matrix ι ι ℝ) : trace (Eᵀ*E)=‖E‖^2 := by
  rw [frobenius_sq]
  simp only [trace,diag,Matrix.mul_apply,Matrix.transpose_apply,←sq]
  rw [Finset.sum_comm]

lemma frobenius_from_traces (E : Matrix ι ι ℝ) {C : ℝ} (hC : 0≤C)
    (h : ∀P : Matrix ι ι ℝ,|trace (P*E)|≤C*‖P‖) : ‖E‖≤C := by
  have H:=h Eᵀ
  rw [trace_square_eq,abs_of_nonneg (sq_nonneg _),Matrix.frobenius_norm_transpose] at H
  nlinarith [norm_nonneg E]

theorem source_taylor_frobenius_bound (E Q : Matrix ι ι ℝ) (s t : ι→ℝ) {C S T B R : ℝ}
    (hC : 0≤C) (hS : 0≤S) (hT : 0≤T) (hB : 0≤B) (hR : 0≤R)
    (hs : (∑i,(s i)^2)≤S^2) (ht : (∑k,(t k)^2)≤T^2)
    (hQ4 : (∑i,∑k,(Q i k)^4)≤B^4) (hQr : ∀i,(∑k,(Q i k)^2)≤R^2)
    (hE : ∀i k,|E i k|≤C*|s i| *((Q i k)^2+|Q i k| * |t k|+(t k)^2)) :
    ‖E‖≤C*S*(B^2+R*T+T^2) := by
  apply frobenius_from_traces E (by positivity)
  intro P
  have H:=source_taylor_trace_bound P E Q s t hC hS hT hB hR hs ht hQ4 hQr hE
  apply H.trans
  nlinarith [mul_le_mul_of_nonneg_right (operator_le_frobenius P)
    (show 0≤C*S*(B^2+R*T+T^2) by positivity)]

theorem source_product_frobenius_bound (E D Q : Matrix ι ι ℝ) (t : ι→ℝ) {C S T R L : ℝ}
    (hC : 0≤C) (hS : 0≤S) (hT : 0≤T) (hR : 0≤R) (hL : 0≤L)
    (hD : (∑i,∑k,(D i k)^2)≤S^2) (ht : (∑k,(t k)^2)≤T^2)
    (hQ : (∑i,∑k,(Q i k)^4)≤R^4) (hQd : (∑i,(Q i i)^2)≤L^2)
    (hE : ∀i k,|E i k|≤C*|D i k| *(|Q i k|+|t k|)) :
    ‖E‖≤C*S*(R+L+T) := by
  apply frobenius_from_traces E (by positivity)
  intro P
  have hP : (∑i,∑k,if i=k then 0 else (P k i)^4)≤‖P‖^4 := by
    have H:=pow_le_pow_left₀ (norm_nonneg (offDiagonalVector P)) (offDiagonalSeminorm_le P) 4
    change offDiagonalSeminorm P ^ 4 ≤ ‖P‖ ^ 4 at H
    rw [offDiagonalSeminorm_fourth,Fintype.sum_prod_type] at H
    rw [Finset.sum_comm]
    simpa only [eq_comm] using H
  have H:=source_product_trace_bound P E D Q t hC hS hT (norm_nonneg P) hR hL
    hD ht hP hQ hQd hE
  apply H.trans
  nlinarith [mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
    (operator_le_frobenius P) (show 0≤L+T by positivity)) (mul_nonneg hC hS)]

lemma rank_one_trace_bound (P : Matrix ι ι ℝ) (u v : EuclideanSpace ℝ ι) :
    |trace (P*Matrix.of (fun i k=>u i*v k))|≤opNorm P*‖u‖*‖v‖ := by
  have H:=abs_real_inner_le_norm v (P.toEuclideanLin.toContinuousLinearMap u)
  have he : trace (P*Matrix.of (fun i k=>u i*v k))=
      inner ℝ v (P.toEuclideanLin.toContinuousLinearMap u) := by
    change (∑i,∑k,P i k*(u k*v i))=∑i,(∑k,P i k*u k)*v i
    simp only [Finset.sum_mul]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro k _; ring
  rw [he]
  apply H.trans
  have h:=mul_le_mul_of_nonneg_left
    (P.toEuclideanLin.toContinuousLinearMap.le_opNorm u) (norm_nonneg v)
  change ‖v‖*‖P.toEuclideanLin.toContinuousLinearMap u‖≤opNorm P*‖u‖*‖v‖
  change ‖v‖*‖P.toEuclideanLin.toContinuousLinearMap u‖≤‖v‖*(opNorm P*‖u‖) at h
  nlinarith only [h]

end SKGap.SourceError

end
end

end OAI
