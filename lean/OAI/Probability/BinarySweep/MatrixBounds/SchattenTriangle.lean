import Mathlib
import OAI.Probability.BinarySweep.MatrixBounds.SchattenBasic

namespace OAI

noncomputable section
open scoped BigOperators Classical Matrix.Norms.L2Operator

namespace BinaryCoordinateSweeps.TraceHolder
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma matrixMoment_sum_le {α : Type*} [Fintype α] {q : ℕ} (hq : 0<q) (A : α → M ι) :
    matrixMoment q (∑a, A a) ≤ (∑a, schatten q (A a))^(2*q) := by
  let B : Fin (2*q) → α → M ι := fun j a => if j.val%2=0 then star (A a) else A a
  have he : (fun j : Fin (2*q) => if j.val%2=0 then star (∑a, A a) else ∑a, A a)=
      fun j => ∑a, B j a := by
    funext j
    dsimp [B]
    split_ifs <;> simp only [star_sum]
  calc
    _ ≤ ‖Matrix.trace ((star (∑a, A a)*(∑a, A a))^q)‖ := Complex.re_le_norm _
    _ = ‖∑x : Fin (2*q) → α, Matrix.trace (List.ofFn (fun j => B j (x j))).prod‖ := by
      rw [← alternating_gram,he,prod_ofFn_sum,Matrix.trace_sum]
    _ ≤ ∑x : Fin (2*q) → α, ‖Matrix.trace (List.ofFn (fun j => B j (x j))).prod‖ := norm_sum_le _ _
    _ ≤ ∑x : Fin (2*q) → α, ∏j, schatten q (A (x j)) := by
      apply Finset.sum_le_sum
      intro x _
      convert matrix_trace_holder hq (fun j => B j (x j)) using 1
      apply Finset.prod_congr rfl
      intro coordinate _
      dsimp [B,schatten]
      split_ifs <;> simp only [matrixMoment_star]
    _ = (∑a, schatten q (A a))^(2*q) := by
      rw [← Fintype.prod_sum (fun (_ : Fin (2*q)) a => schatten q (A a))]
      simp

lemma schatten_mul_left {q : ℕ} (hq : 0<q) (C A : M ι) :
    schatten q (C*A) ≤ ‖C‖*schatten q A := by
  apply (pow_le_pow_iff_left₀ (schatten_nonneg _ _)
      (mul_nonneg (norm_nonneg _) (schatten_nonneg _ _)) (by omega : 2*q≠0)).mp
  rw [mul_pow,schatten_pow hq,schatten_pow hq]
  exact matrixMoment_mul_left hq C A

lemma schatten_mul_right {q : ℕ} (hq : 0<q) (A C : M ι) :
    schatten q (A*C) ≤ schatten q A*‖C‖ := by
  rw [← schatten_star q (A*C),star_mul]
  simpa only [norm_star,schatten_star,mul_comm] using schatten_mul_left hq (star C) (star A)

lemma norm_le_schatten {q : ℕ} (hq : 0<q) (A : M ι) : ‖A‖≤ schatten q A := by
  by_cases hz : matrixMoment q A=0
  · rw [(matrixMoment_eq_zero_iff hq A).mp hz,norm_zero]
    exact schatten_nonneg _ _
  have ht := lt_of_le_of_ne (matrixMoment_nonneg q A) (Ne.symm hz)
  obtain ⟨U,V,d,hU,hV,hd,hs,he⟩ := normalized_svd hq A ht
  have hd1 : ∀i, d i≤ 1 := by
    intro i
    rw [← hs]
    exact Finset.single_le_sum (fun j _ => hd j) (Finset.mem_univ i)
  have hD : ‖diagPower d ((((2*q:ℕ):ℝ)⁻¹:ℝ):ℂ)‖≤ 1 :=
    diagPower_norm_le_one d hd hd1 (by simp)
  conv_lhs => rw [he,norm_smul,Real.norm_eq_abs]
  change |schatten q A| * _ ≤ schatten q A
  rw [abs_of_nonneg (schatten_nonneg q A)]
  apply mul_le_of_le_one_right (schatten_nonneg _ _)
  refine (norm_mul_le _ _).trans ((mul_le_of_le_one_left (norm_nonneg _) ?_).trans hV)
  exact (norm_mul_le _ _).trans ((mul_le_of_le_one_left (norm_nonneg _) hU).trans hD)

lemma schatten_sandwich {q : ℕ} (hq : 0<q) (A B C : M ι) :
    schatten q (A*B*C)≤ schatten q A*‖B‖*schatten q C := by
  exact (schatten_mul_right hq (A*B) C).trans
    ((mul_le_mul_of_nonneg_right (schatten_mul_right hq A B) (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left (norm_le_schatten hq C)
        (mul_nonneg (schatten_nonneg _ _) (norm_nonneg _))))

end BinaryCoordinateSweeps.TraceHolder

end

end OAI
