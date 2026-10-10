import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fintype.Perm
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Positivity
import Mathlib.Basic.Real.Basic

namespace OAI

/-!
# Ordering the moment tuples in the laminar counting lemma

Each tuple has a sorting permutation. Summing over all permutations and
then reindexing the tuple sum gives the factorial overcount in §6,
`count:moment`, including repeated occurrences and repeated intervals.
-/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

variable {ι α : Type*} [Fintype ι] [LinearOrder α]

omit [Fintype ι] in
theorem tuple_comp_perm_bijective {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Function.Bijective (fun a : Fin n → ι => a ∘ σ) := by
  constructor
  · intro a b hab
    funext i
    have h := congrFun hab (σ.symm i)
    simpa only [Function.comp_apply, σ.apply_symm_apply] using h
  · intro a
    refine ⟨a ∘ σ.symm, ?_⟩
    funext i
    simp only [Function.comp_apply, σ.symm_apply_apply]

/-- A nonnegative permutation-invariant tuple weight loses at most `n!`
when the tuple sum is restricted to one monotone ordering. -/
theorem sum_tuple_le_factorial_sum_sorted (rank : ι → α) (n : ℕ)
    (w : (Fin n → ι) → ℝ) (hw : ∀ a, 0 ≤ w a)
    (hperm : ∀ (a : Fin n → ι) (σ : Equiv.Perm (Fin n)), w (a ∘ σ) = w a) :
    (∑ a : Fin n → ι, w a) ≤
      (n.factorial : ℝ) * ∑ a : Fin n → ι, if Monotone (rank ∘ a) then w a else 0 := by
  classical
  have hpoint (a : Fin n → ι) : w a ≤
      ∑ σ : Equiv.Perm (Fin n), if Monotone (rank ∘ (a ∘ σ)) then w (a ∘ σ) else 0 := by
    let σ := Tuple.sort (rank ∘ a)
    have hsorted : Monotone (rank ∘ (a ∘ σ)) := Tuple.monotone_sort (rank ∘ a)
    calc
      w a = if Monotone (rank ∘ (a ∘ σ)) then w (a ∘ σ) else 0 := by
        rw [ite_eq_left hsorted, hperm]
      _ ≤ _ := Finset.single_le_sum (a := σ) (f := fun τ : Equiv.Perm (Fin n) =>
          if Monotone (rank ∘ (a ∘ τ)) then w (a ∘ τ) else 0) (fun τ _ => by
          split_ifs
          · exact hw _
          · exact le_rfl)
        (Finset.mem_univ σ)
  calc
    (∑ a : Fin n → ι, w a) ≤ ∑ a : Fin n → ι,
        ∑ σ : Equiv.Perm (Fin n), if Monotone (rank ∘ (a ∘ σ)) then w (a ∘ σ) else 0 :=
      Finset.sum_le_sum fun a _ => hpoint a
    _ = ∑ σ : Equiv.Perm (Fin n), ∑ a : Fin n → ι,
        if Monotone (rank ∘ (a ∘ σ)) then w (a ∘ σ) else 0 := Finset.sum_comm
    _ = ∑ _σ : Equiv.Perm (Fin n), ∑ a : Fin n → ι,
        if Monotone (rank ∘ a) then w a else 0 := by
      apply Finset.sum_congr rfl
      intro σ _
      exact Fintype.sum_bijective _ (tuple_comp_perm_bijective σ) _ _ (fun _ => rfl)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
        nsmul_eq_mul]

end LipschitzHilbert

end

end OAI
