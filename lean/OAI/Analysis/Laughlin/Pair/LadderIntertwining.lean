import OAI.Analysis.Laughlin.Pair.Orthonormality
import OAI.Analysis.Laughlin.Pair.TensorBoundary
import OAI.Analysis.Laughlin.Spin.LadderMatrix

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

noncomputable def pairInclusion (Q : ℕ) :
    Matrix (Fin (Q+1) × Fin (Q+1)) (Fin ((2*Q-2)+1)) ℝ :=
  fun i p => pairCoefficient Q p.val i.1 i.2

theorem pairInclusion_raising (Q : ℕ) (hQ : 0 < Q) :
    totalRaise Q Q * pairInclusion Q = pairInclusion Q * raiseMatrix (2*Q-2) := by
  ext i p
  change (∑ j, totalRaise Q Q i j*pairCoefficient Q p.val j.1 j.2) =
    ∑ k, pairCoefficient Q k.val i.1 i.2 * raiseMatrix (2*Q-2) k p
  rw [totalRaise_apply,raiseMatrix_row,raiseMatrix_row,raiseMatrix_column]
  change pairTensorRaise Q p.val i.1 i.2 = _
  by_cases hp : 0 < p.val
  · rw [dite_eq_left hp]
    have he := pairCoefficient_tensor_raising Q (p.val-1) hQ (by omega) i.1 i.2
    rw [show p.val-1+1=p.val by omega] at he
    simpa only [mul_comm] using he
  · rw [dite_eq_right hp]
    have hz : p.val=0 := by omega
    rw [hz,pairCoefficient_tensor_highest Q hQ]

theorem pairInclusion_lowering (Q : ℕ) (hQ : 0 < Q) :
    (totalRaise Q Q)ᵀ * pairInclusion Q = pairInclusion Q * (raiseMatrix (2*Q-2))ᵀ := by
  ext i p
  change (∑ j, totalRaise Q Q j i*pairCoefficient Q p.val j.1 j.2) =
    ∑ k, pairCoefficient Q k.val i.1 i.2 * raiseMatrix (2*Q-2) p k
  conv_rhs => simp only [mul_comm (pairCoefficient Q _ _ _)]
  rw [totalRaise_transpose_apply,raiseMatrix_column,raiseMatrix_column,raiseMatrix_row]
  have heq :
      (if h : 0 < i.1.val then pairCoefficient Q p.val ⟨i.1.val-1,by omega⟩ i.2 *
        ladder Q (i.1.val-1) else 0) +
      (if h : 0 < i.2.val then pairCoefficient Q p.val i.1 ⟨i.2.val-1,by omega⟩ *
        ladder Q (i.2.val-1) else 0) = pairTensorLower Q p.val i.1 i.2 := by
    unfold pairTensorLower
    split_ifs <;> ring
  rw [heq]
  by_cases hp : p.val < 2*Q-2
  · rw [dite_eq_left hp,pairCoefficient_tensor_lowering Q p.val hQ hp]
  · rw [dite_eq_right hp]
    have hz : p.val=2*Q-2 := by omega
    rw [hz,pairCoefficient_tensor_lowest Q hQ]

theorem pairInclusion_isometry (Q : ℕ) (hQ : 2 ≤ Q) :
    (pairInclusion Q)ᵀ * pairInclusion Q = 1 := by
  ext p q
  rw [Matrix.mul_apply,Fintype.sum_prod_type]
  simp only [Matrix.transpose_apply,pairInclusion,Matrix.one_apply]
  have h := pairCoefficient_gram Q p.val q.val hQ (by omega)
  simpa only [Fin.ext_iff] using h

theorem pairInclusion_transpose_raising (Q : ℕ) (hQ : 0 < Q) :
    (pairInclusion Q)ᵀ * totalRaise Q Q = raiseMatrix (2*Q-2) * (pairInclusion Q)ᵀ := by
  have h := congrArg Matrix.transpose (pairInclusion_lowering Q hQ)
  simpa only [Matrix.transpose_mul,Matrix.transpose_transpose] using h

end Laughlin.Spin

end OAI
