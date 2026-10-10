import Mathlib
import OAI.LinearAlgebra.MatrixFields.Extraction.JointMaskedSelection

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section
namespace MatrixMultiplication.JointCoarseReorder
open JointCoarseHashing
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def tripleSide {P : Type*} (s : Fin 3) (t : Triple P) : Word P :=
  (Matrix.vecCons (t.1) (Matrix.vecCons (t.2.1) (Matrix.vecCons (t.2.2) Matrix.vecEmpty))) s

def reorder {P : Type*} (sigma : Equiv.Perm (Fin 3)) (t : Triple P) : Triple P :=
  (tripleSide (sigma 0) t, tripleSide (sigma 1) t, tripleSide (sigma 2) t)

@[simp] theorem tripleSide_reorder {P : Type*} (sigma : Equiv.Perm (Fin 3))
    (t : Triple P) (s : Fin 3) :
    tripleSide s (reorder sigma t) = tripleSide (sigma s) t := by
  fin_cases s <;> rfl

theorem reorder_injective {P : Type*} (sigma : Equiv.Perm (Fin 3)) :
    Function.Injective (reorder (P := P) sigma) := by
  intro t u h
  have hs (s : Fin 3) : tripleSide s t = tripleSide s u := by
    have hh := congrArg (tripleSide (sigma.symm s)) h
    simpa only [tripleSide_reorder, sigma.apply_symm_apply] using hh
  exact Prod.ext (hs 0) (Prod.ext (hs 1) (hs 2))

theorem reorder_support {P : Type*} (sigma : Equiv.Perm (Fin 3)) (S : P → ℕ)
    (t : Triple P) (ht : HasSupportSum S t) : HasSupportSum S (reorder sigma t) := by
  intro p
  have hsum : (∑ i : Fin 3, (tripleSide (sigma i) t p).val) =
      ∑ i : Fin 3, (tripleSide i t p).val :=
    Equiv.sum_comp sigma (fun i : Fin 3 => (tripleSide i t p).val)
  simpa [reorder, tripleSide, Fin.sum_univ_succ, Nat.add_assoc] using hsum.trans (by
    simpa [tripleSide, Fin.sum_univ_succ, Nat.add_assoc] using ht p)

end MatrixMultiplication.JointCoarseReorder

end

end MatrixAllFields

end OAI
