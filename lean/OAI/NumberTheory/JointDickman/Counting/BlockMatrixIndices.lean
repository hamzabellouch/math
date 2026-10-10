import OAI.NumberTheory.JointDickman.Counting.ArithmeticBlockAverage

namespace OAI

/-! # The block positions as a finite matrix index type -/

namespace JointDickman
open Finset

def blockIndexEquiv (M : ℕ) : Fin M ≃ (Icc (1 : ℤ) M) where
  toFun i := ⟨(i.val : ℤ)+1, mem_Icc.mpr ⟨by omega,by have h := i.isLt; omega⟩⟩
  invFun i := ⟨(i.val-1).toNat,by have h := mem_Icc.mp i.property; omega⟩
  left_inv i := by apply Fin.ext; simp
  right_inv i := by apply Subtype.ext; have h := mem_Icc.mp i.property; dsimp; omega

theorem sum_block_indices (M : ℕ) (f : ℤ → ℝ) :
    (∑ i : Fin M, f ((i.val : ℤ)+1)) = ∑ i ∈ Icc (1 : ℤ) M, f i := by
  calc
    _ = ∑ i : (Icc (1 : ℤ) M), f i.val := (blockIndexEquiv M).sum_comp (fun i => f i.val)
    _ = _ := sum_coe_sort _ _

end JointDickman

end OAI
