import Mathlib.LinearAlgebra.Multilinear.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Fin

namespace OAI

/-! # Multilinear evaluation annihilates the abelian bar boundary

Contracting two adjacent entries by addition is the sum of the evaluations
with either entry deleted. The alternating boundary sum then telescopes.
-/

noncomputable section
namespace PolycyclicRecognition
variable {R M W : Type} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup W] [Module R W]

theorem multilinear_contractNth_add {n : ℕ}
    (F : MultilinearMap R (fun _ : Fin n => M) W) (v : Fin (n + 1) → M) (j : Fin n) :
    F (Fin.contractNth j.castSucc (· + ·) v) =
      F (v ∘ j.castSucc.succAbove) + F (v ∘ j.succ.succAbove) := by
  classical
  let u := v ∘ j.castSucc.succAbove
  have he : Fin.contractNth j.castSucc (· + ·) v =
      Function.update u j (v j.castSucc + v j.succ) := by
    funext k
    by_cases hkj : k = j
    · subst k
      rw [Function.update_self, Fin.contractNth_apply_of_eq _ _ _ _ rfl]
    · rw [Function.update_of_ne hkj]
      exact Fin.contractNth_apply_of_ne _ _ _ _ (by
        intro hval
        exact hkj (Fin.ext hval.symm))
  have hu : u j = v j.succ := by
    simp [u, Fin.succAbove]
  have hleft : Function.update u j (v j.castSucc) = v ∘ j.succ.succAbove := by
    funext k
    by_cases hkj : k = j
    · subst k
      simp [Fin.succAbove, Fin.lt_def]
    · rw [Function.update_of_ne hkj]
      dsimp [u]
      congr 1
      apply Fin.ext
      have hval : k.val ≠ j.val := by intro he; exact hkj (Fin.ext he)
      simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc, Fin.val_succ]
      split_ifs <;> simp_all only [Fin.val_castSucc, Fin.val_succ] <;> omega
  rw [he, F.map_update_add, hleft, ← hu, Function.update_eq_self]
  exact add_comm _ _

theorem alternating_adjacent_sum {n : ℕ} (w : Fin (n + 1) → W) :
    w 0 + (∑ j : Fin n, (-1 : ℤ) ^ (j.val + 1) • (w j.castSucc + w j.succ)) +
      (-1 : ℤ) ^ (n + 1) • w (Fin.last n) = 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := ih (w ∘ Fin.castSucc)
    rw [Fin.sum_univ_castSucc]
    simp only [Function.comp_apply, Fin.castSucc_zero, Fin.val_castSucc] at h ⊢
    have hs : (-1 : ℤ) ^ (n + 1 + 1) = -((-1 : ℤ) ^ (n + 1)) := by
      rw [pow_succ, mul_neg_one]
    rw [hs, neg_smul, smul_add]
    have he : (Fin.last n).succ = Fin.last (n + 1) := rfl
    rw [he]
    simpa only [Fin.val_last, Fin.succ_castSucc, add_assoc, add_neg_cancel, add_zero] using h

theorem contractNth_last_eq {α : Type} {n : ℕ} (op : α → α → α)
    (v : Fin (n + 1) → α) :
    Fin.contractNth (Fin.last n) op v = v ∘ Fin.castSucc := by
  funext k
  exact Fin.contractNth_apply_of_lt _ _ _ _ k.isLt

theorem multilinear_abelian_bar_boundary {n : ℕ}
    (F : MultilinearMap R (fun _ : Fin n => M) W) (v : Fin (n + 1) → M) :
    F (fun i => v i.succ) +
      (∑ j : Fin (n + 1), (-1 : ℤ) ^ (j.val + 1) • F (Fin.contractNth j (· + ·) v)) = 0 := by
  have h := alternating_adjacent_sum (fun j : Fin (n + 1) => F (v ∘ j.succAbove))
  rw [Fin.sum_univ_castSucc]
  simp only [multilinear_contractNth_add, Fin.val_last, contractNth_last_eq]
  simpa only [Fin.succAbove_zero, Fin.succAbove_last, Fin.val_castSucc,
    Function.comp_def, add_assoc] using h

end PolycyclicRecognition

end

end OAI
