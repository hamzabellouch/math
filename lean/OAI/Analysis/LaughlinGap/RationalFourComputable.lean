import Mathlib
import OAI.Analysis.LaughlinGap.RationalFourRows
import OAI.Analysis.LaughlinGap.RationalRowComputable

namespace OAI

/-! Rational Four Computable. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators
open Spin

def RationalRow.fourSumFast (r : RationalRow) (D s : ℕ) (i k : Fin 9) : ℚ :=
  ∑ p : Fin 8, if h : p.val ≤ r.t.val+i.val ∧ r.t.val+i.val-p.val < 9 then
    r.alpha p ⟨r.t.val+i.val-p.val,h.2⟩ *
      vCoefficient D (r.t.val+i.val+k.val) s p.val (r.t.val+i.val-p.val) k.val *
        (2:ℚ)^((s+1)/2+p.val) else 0

lemma RationalRow.fourSum_eq_fast (r : RationalRow) (D s : ℕ) (i k : Fin 9) :
    r.fourSum D s i k = r.fourSumFast D s i k := by
  rw [RationalRow.fourSum,sum_row_fiber r.t i (fun p j =>
    r.alpha p j * vCoefficient D (r.t.val+i.val+k.val) s p.val j.val k.val *
      (2:ℚ)^((s+1)/2+p.val))]
  simp only [sum_fixed_pair,RationalRow.fourSumFast]

def RationalRow.fourMatrixFast (r : RationalRow) (D u v : ℕ) : ℚ :=
  -(∑ i : Fin 9, ∑ k : Fin 9, fourRowFactor r.t.val D i.val k.val *
    r.fourSumFast D u i k * r.fourSumFast D v k i)

lemma RationalRow.fourMatrix_eq_fast (r : RationalRow) (D : ℕ) (u v : FourCopy D) :
    r.fourMatrix D u v = r.fourMatrixFast D u.val.val v.val.val := by
  simp only [RationalRow.fourMatrix,RationalRow.fourMatrixFast,RationalRow.fourSum_eq_fast]

def fourCopyEquiv (D : ℕ) : FourCopy D ≃ Fin ((D+1)/2) where
  toFun r := ⟨r.val.val/2, by have := r.val.isLt; obtain ⟨k,hk⟩ := r.property; omega⟩
  invFun i := ⟨⟨2*i.val+1,by have := i.isLt; omega⟩,⟨i.val,by rfl⟩⟩
  left_inv r := by
    apply Subtype.ext; apply Fin.ext
    have := r.property
    obtain ⟨k,hk⟩ := this
    dsimp
    omega
  right_inv i := by apply Fin.ext; dsimp; omega

@[simp] lemma fourCopyEquiv_symm_val (D : ℕ) (i : Fin ((D+1)/2)) :
    ((fourCopyEquiv D).symm i).val.val = 2*i.val+1 := rfl

end LaughlinGap.RealOccupation

end

end OAI
