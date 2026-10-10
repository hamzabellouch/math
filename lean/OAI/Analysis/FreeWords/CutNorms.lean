import Mathlib
import OAI.Analysis.FreeWords.CutTuples
import OAI.Analysis.FreeWords.TupleMatrices

namespace OAI

noncomputable section

namespace KKFreeWords

open scoped BigOperators ComplexOrder InnerProductSpace

noncomputable section

variable {E α : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

variable [Fintype α] [DecidableEq α]

omit [CompleteSpace E] in
theorem sum_noPresCut_norm (p q : ℕ) (W : Multiset α)
    (C D : Fin (q+p) → α → E →L[ℂ] E) {t : ℝ} (ht : 0 ≤ t)
    (hC : ∀ j, RowSqBound (C j) (t^2)) (hD : ∀ j, ColSqBound (D j) (t^2)) :
    ‖∑ a : Fin (q+p) → α, if tupleLabels a = W then
      noPresCut (fun j => C j (a j)) (fun j => D j (a j)) q else 0‖ ≤
      Real.sqrt ((q.factorial : ℝ) * p.factorial) * t^(q+p) := by
  rw [sum_noPresCut]
  have hCr : RowSqBound (tupleOp (fun j : Fin q => C (j.castAdd p))) ((t^q)^2) := by
    simpa only [← pow_mul, Nat.mul_comm] using
      tupleOp_row (sq_nonneg t) (fun j : Fin q => hC (j.castAdd p))
  have hDc : ColSqBound (tupleOp (fun j : Fin p => D (Fin.natAdd q j))) ((t^p)^2) := by
    simpa only [← pow_mul, Nat.mul_comm] using
      tupleOp_col (sq_nonneg t) (fun j : Fin p => hD (Fin.natAdd q j))
  have hT : MatrixSqBound (tupleScalarMatrix (E := E) p q W)
      ((Real.sqrt ((q.factorial : ℝ)*p.factorial))^2) := by
    rw [Real.sq_sqrt (by positivity), mul_comm]
    exact tupleScalarMatrix_bound p q W
  have h := row_matrix_col_norm hCr hT hDc (pow_nonneg ht _) (Real.sqrt_nonneg _)
    (pow_nonneg ht _)
  change ‖∑ a, ∑ b, tupleOp _ a * tupleScalarMatrix (E := E) p q W a b * tupleOp _ b‖ ≤ _
  exact h.trans_eq (by rw [pow_add]; ring)

theorem sum_presCut_norm (p q : ℕ) (W : Multiset α)
    (C D K : Fin (q+(p+1)) → α → E →L[ℂ] E) {t : ℝ} (ht : 0 ≤ t)
    (hC : ∀ j, RowSqBound (C j) (t^2)) (hD : ∀ j, ColSqBound (D j) (t^2))
    (P : α → E →L[ℂ] E) (hP : ∀ c, IsStarProjection (P c))
    (horth : ∀ c e, c ≠ e → P c * P e = 0) (hsum : ∑ c, P c = 1)
    (Q : E →L[ℂ] E) (hQ : ‖Q‖ ≤ 1) (z : ℂ)
    (hK : ∀ c, K (Fin.natAdd q 0) c = Q * (P c - z • 1) * Q) :
    ‖∑ a : Fin (q+(p+1)) → α, if tupleLabels a = W then
      presCut (fun j => C j (a j)) (fun j => D j (a j)) (fun j => K j (a j))
        (Fin.natAdd q 0) else 0‖ ≤
      (Real.sqrt ((q.factorial : ℝ) * p.factorial) +
        ‖z‖ * Real.sqrt (((q+1).factorial : ℝ) * (p+1).factorial)) * t^(q+p) := by
  rw [sum_presCut]
  have hCr : RowSqBound (tupleOp (fun j : Fin q => C (j.castAdd (p+1)))) ((t^q)^2) := by
    simpa only [← pow_mul, Nat.mul_comm] using
      tupleOp_row (sq_nonneg t) (fun j : Fin q => hC (j.castAdd (p+1)))
  have hDc : ColSqBound (tupleOp (fun j : Fin p => D (Fin.natAdd q j.succ))) ((t^p)^2) := by
    simpa only [← pow_mul, Nat.mul_comm] using
      tupleOp_col (sq_nonneg t) (fun j : Fin p => hD (Fin.natAdd q j.succ))
  have hT := tuplePresMatrix_bound P hP horth hsum Q hQ z p q W
  have h := row_matrix_col_norm hCr hT hDc (pow_nonneg ht _) (by positivity)
    (pow_nonneg ht _)
  have he : (fun a : Fin q → α => fun b : Fin p → α =>
      ∑ c, if tupleLabels a + {c} + tupleLabels b = W then K (Fin.natAdd q 0) c else 0) =
      tuplePresMatrix P Q z p q W := by
    funext a b
    simp only [tuplePresMatrix, hK]
  change ‖∑ a, ∑ b, tupleOp _ a * _ * tupleOp _ b‖ ≤ _
  simp only [hK]
  exact h.trans_eq (by rw [pow_add]; simp only [mul_comm (p.factorial : ℝ),
    mul_comm (((p+1).factorial : ℕ) : ℝ)]; ring)

end

end KKFreeWords
end

end OAI
