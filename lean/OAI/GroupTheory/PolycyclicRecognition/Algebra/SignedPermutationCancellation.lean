import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace OAI

/-! # Cancellation of signed sums fixed by an adjacent transposition -/

noncomputable section
namespace PolycyclicRecognition
open Equiv
variable {I V : Type} [Fintype I] [DecidableEq I] [AddCommGroup V]

theorem signed_sum_of_swap_invariant (a b : I) (hab : a ≠ b)
    (f : Equiv.Perm I → V) (hf : ∀ σ, f (σ * Equiv.swap a b) = f σ) :
    ∑ σ : Equiv.Perm I, (Equiv.Perm.sign σ : ℤ) • f σ = 0 := by
  classical
  apply Finset.sum_ninvolution (fun σ => σ * Equiv.swap a b)
  · intro σ
    rw [hf]
    simp [map_mul, Equiv.Perm.sign_swap hab]
  · intro σ _ hfix
    have hs : Equiv.swap a b = (1 : Equiv.Perm I) :=
      mul_left_cancel (hfix.trans (mul_one σ).symm)
    have h := Equiv.congr_fun hs a
    apply hab
    simpa using h.symm
  · intro σ
    exact Finset.mem_univ _
  · intro σ
    simp [mul_assoc]

end PolycyclicRecognition

end

end OAI
