import OAI.Combinatorics.ContingencyTables.Model
import Mathlib.Algebra.BigOperators.Group.Finset.Pi

namespace OAI

/-! # Relabeling a rectangular completion, preserving every table -/

namespace ContingencyTables

open scoped BigOperators

variable {I J I' J' : Type*} [Fintype I] [Fintype J] [Fintype I'] [Fintype J']

def tableReindex (eI : I' ≃ I) (eJ : J' ≃ J) (r : I → ℕ) (c : J → ℕ) :
    Table r c ≃ Table (fun i => r (eI i)) (fun j => c (eJ j)) where
  toFun X := ⟨fun i j => X.val (eI i) (eJ j),
    fun i => (eJ.sum_comp (X.val (eI i))).trans (X.property.1 (eI i)),
    fun j => (eI.sum_comp (fun i => X.val i (eJ j))).trans (X.property.2 (eJ j))⟩
  invFun X := ⟨fun i j => X.val (eI.symm i) (eJ.symm j),by
    constructor
    · intro i
      rw [eJ.symm.sum_comp]
      simpa only [Equiv.apply_symm_apply] using X.property.1 (eI.symm i)
    · intro j
      exact (eI.symm.sum_comp (fun i => X.val i (eJ.symm j))).trans (by
        simpa only [Equiv.apply_symm_apply] using X.property.2 (eJ.symm j))⟩
  left_inv X := by
    apply Subtype.ext
    funext i j
    simp only [Equiv.apply_symm_apply]
  right_inv X := by
    apply Subtype.ext
    funext i j
    simp only [Equiv.symm_apply_apply]

end ContingencyTables

end OAI
