import OAI.GroupTheory.PolycyclicRecognition.Algebra.SignedPermutationCancellation
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finsupp.Basic

namespace OAI

/-! # Adjacent and endpoint cancellations in alternating abelian bar chains -/

noncomputable section
namespace PolycyclicRecognition
variable {A : Type} [CommGroup A]

theorem contractNth_adjacent_swap {n : ℕ} (v : Fin (n + 1) → A) (j : Fin n) :
    Fin.contractNth j.castSucc (· * ·) (v ∘ Equiv.swap j.castSucc j.succ) =
      Fin.contractNth j.castSucc (· * ·) v := by
  funext k
  rcases lt_trichotomy k.val j.val with hlt | heq | hgt
  · rw [Fin.contractNth_apply_of_lt _ _ _ _ hlt,
      Fin.contractNth_apply_of_lt _ _ _ _ hlt]
    have h₁ : k.castSucc ≠ j.castSucc := by intro h; have := congrArg Fin.val h; dsimp at this; omega
    have h₂ : k.castSucc ≠ j.succ := by intro h; have := congrArg Fin.val h; dsimp at this; omega
    simp only [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne h₁ h₂]
  · have hkj : k = j := Fin.ext heq
    subst k
    rw [Fin.contractNth_apply_of_eq _ _ _ _ rfl,
      Fin.contractNth_apply_of_eq _ _ _ _ rfl]
    have hne : j.castSucc ≠ j.succ := by intro h; have := congrArg Fin.val h; dsimp at this; omega
    simp only [Function.comp_apply, Equiv.swap_apply_left, Equiv.swap_apply_right]
    exact mul_comm _ _
  · rw [Fin.contractNth_apply_of_gt _ _ _ _ hgt,
      Fin.contractNth_apply_of_gt _ _ _ _ hgt]
    have h₁ : k.succ ≠ j.castSucc := by intro h; have := congrArg Fin.val h; dsimp at this; omega
    have h₂ : k.succ ≠ j.succ := by intro h; have := congrArg Fin.val h; dsimp at this; omega
    simp only [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne h₁ h₂]

theorem alternatingBar_interior_cancel {n : ℕ} (v : Fin (n + 1) → A) (j : Fin n) :
    (∑ σ : Equiv.Perm (Fin (n + 1)), (Equiv.Perm.sign σ : ℤ) •
      Finsupp.single (Fin.contractNth j.castSucc (· * ·) (v ∘ σ)) (1 : ℤ)) = 0 := by
  have hne : j.castSucc ≠ j.succ := by intro h; have := congrArg Fin.val h; dsimp at this; omega
  apply signed_sum_of_swap_invariant j.castSucc j.succ hne
  intro σ
  congr 1
  exact contractNth_adjacent_swap (v ∘ σ) j

end PolycyclicRecognition

end

end OAI
