import Mathlib

namespace OAI

/-! Calabi Tensor Algebra. -/

section

 

noncomputable section
open Matrix
open scoped ComplexOrder MatrixOrder
namespace KaehlerCalculus
variable {n : ℕ}
abbrev ConnectionTensor (n : ℕ) := Fin n → Matrix (Fin n) (Fin n) ℂ

def tensorPairAt (P M : Matrix (Fin n) (Fin n) ℂ) (T U : ConnectionTensor n) : ℂ :=
  ∑ i, ∑ j, P i j * (T i*P*(U j)ᴴ*M).trace

lemma tensorPairAt_one (T U : ConnectionTensor n) : tensorPairAt 1 1 T U =
    ∑ i, (T i*(U i)ᴴ).trace := by
  simp [tensorPairAt,Matrix.one_apply]

lemma tensorPairAt_add_left (P M : Matrix (Fin n) (Fin n) ℂ) (T U W : ConnectionTensor n) :
    tensorPairAt P M (fun i => T i+U i) W = tensorPairAt P M T W+tensorPairAt P M U W := by
  simp only [tensorPairAt,add_mul,Matrix.trace_add,mul_add,Finset.sum_add_distrib]

lemma tensorPairAt_sub_left (P M : Matrix (Fin n) (Fin n) ℂ) (T U W : ConnectionTensor n) :
    tensorPairAt P M (fun i => T i-U i) W = tensorPairAt P M T W-tensorPairAt P M U W := by
  simp only [tensorPairAt,sub_mul,Matrix.trace_sub,mul_sub,Finset.sum_sub_distrib]

lemma tensorPairAt_conj {P M : Matrix (Fin n) (Fin n) ℂ} (hP : P.IsHermitian)
    (hM : M.IsHermitian) (T U : ConnectionTensor n) :
    star (tensorPairAt P M T U) = tensorPairAt P M U T := by
  simp only [tensorPairAt,star_sum,star_mul,← Matrix.trace_conjTranspose,
    Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,hM.eq,hP.eq]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [← hP.apply i j]
  have hc : (M*(U i*(P*(T j)ᴴ))).trace = (U i*P*(T j)ᴴ*M).trace := by
    simpa only [mul_assoc] using Matrix.trace_mul_comm M (U i*P*(T j)ᴴ)
  rw [hc]
  ring

lemma tensorPairAt_self_real {P M : Matrix (Fin n) (Fin n) ℂ} (hP : P.IsHermitian)
    (hM : M.IsHermitian) (T : ConnectionTensor n) :
    (tensorPairAt P M T T).im = 0 := by
  have he := congrArg Complex.im (tensorPairAt_conj hP hM T T)
  simp only [Complex.star_def,Complex.conj_im] at he
  linarith

lemma matrix_contraction_reindex (P C : Matrix (Fin n) (Fin n) ℂ)
    (Q : Fin n → Fin n → ℂ) :
    (∑ i, ∑ j, (C*P) i j*Q i j) = ∑ i, ∑ j, P i j * ∑ q, C q i*Q q j := by
  simp only [Matrix.mul_apply,Finset.sum_mul,Finset.mul_sum]
  calc
    (∑ i, ∑ j, ∑ q, C i q*P q j*Q i j) =
        ∑ q, ∑ j, ∑ i, C i q*P q j*Q i j := by
      trans ∑ i, ∑ q, ∑ j, C i q*P q j*Q i j
      · apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro q _
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro q _
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      ring

lemma covariant_pair_algebra (P M C : Matrix (Fin n) (Fin n) ℂ)
    (T U A B : ConnectionTensor n) :
    (∑ i, ∑ j, (-(C*P) i j*(T i*P*(U j)ᴴ*M).trace+
      P i j*(A i*P*(U j)ᴴ*M-T i*C*P*(U j)ᴴ*M+
        T i*P*(B j)ᴴ*M+T i*P*(U j)ᴴ*M*C).trace)) =
      tensorPairAt P M (fun i => A i+C*T i-T i*C-∑ q, C q i • T q) U +
        tensorPairAt P M T B := by
  have hc (i j) : (C*T i*P*(U j)ᴴ*M).trace = (T i*P*(U j)ᴴ*M*C).trace := by
    simpa only [mul_assoc] using Matrix.trace_mul_comm C (T i*P*(U j)ᴴ*M)
  simp only [tensorPairAt,sub_mul,add_mul,Matrix.sum_mul,Matrix.smul_mul,
    Matrix.trace_add,Matrix.trace_sub,Matrix.trace_sum,Matrix.trace_smul,smul_eq_mul,
    hc,mul_add,mul_sub,Finset.sum_add_distrib,Finset.sum_sub_distrib,
    neg_mul,Finset.sum_neg_distrib]
  rw [matrix_contraction_reindex P C (fun i j => (T i*P*(U j)ᴴ*M).trace)]
  ring
end KaehlerCalculus

end
end

end OAI
