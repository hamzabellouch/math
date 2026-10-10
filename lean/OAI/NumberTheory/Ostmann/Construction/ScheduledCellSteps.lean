import OAI.NumberTheory.Ostmann.Construction.InitialScheduledPrior
import OAI.NumberTheory.Ostmann.Construction.SelectedCompensationPrior

namespace OAI

/-! # The actual selected cell removed by each transfer -/
namespace Ostmann
open scoped Classical

theorem scheduledRegularPrior_restore {A : Type} (cell : ℕ → A → ℝ)
    (bulk : A → ℝ) (top c : ℕ) (cs : List ℕ) (n m : ℕ) :
    scheduledRegularPrior cell bulk top (c :: cs) n m =
      movingTemplateRestoredPrior n (scheduledSmallLength cs) m (cell c)
        (scheduledRegularPrior cell bulk top cs n m) := by
  funext i
  rcases i with ⟨j, i | i⟩
  · refine Fin.addCases (fun t => ?_) (fun t => ?_) i
    · simp only [scheduledRegularPrior, scheduledSmallCell, movingTemplateRestoredPrior,
        movingReverseTemplate, Equiv.coe_fn_symm_mk, Sum.elim_inl, Fin.addCases_left]
      exact congrArg cell (Fin.append_left _ _ t)
    · simp only [scheduledRegularPrior, scheduledSmallCell, movingTemplateRestoredPrior,
        movingReverseTemplate, Equiv.coe_fn_symm_mk, Sum.elim_inl, Sum.elim_inr,
        Fin.addCases_right]
      exact congrArg cell (Fin.append_right _ _ t)
  · rfl

theorem scheduledRegularPrior_doubled {A : Type} (cell : ℕ → A → ℝ)
    (bulk : A → ℝ) (top : ℕ) (cs : List ℕ) (n m : ℕ) :
    movingTemplateDoubledPrior n (scheduledSmallLength cs) m
      (scheduledRegularPrior cell bulk top cs n m) =
      scheduledRegularPrior cell bulk top cs (n + 1) m := rfl

theorem drop_eq_headD_cons {A : Type} (cs : List A) (fallback : A) (n : ℕ)
    (hn : n < cs.length) :
    cs.drop n = (cs.drop n).headD fallback :: cs.drop (n + 1) := by
  induction cs generalizing n with
  | nil => simp at hn
  | cons c cs ih =>
    cases n with
    | zero => simp
    | succ n =>
      simpa only [List.drop_succ_cons] using ih n (by simpa using hn)

theorem scheduledSmallLength_drop_step (cs : List ℕ) (n : ℕ) (hn : n < cs.length) :
    scheduledSmallLength (cs.drop n) = 4 + scheduledSmallLength (cs.drop (n + 1)) := by
  conv_lhs => rw [drop_eq_headD_cons cs 0 n hn]
  rfl

theorem initial_scheduled_length (top : ℕ) (cs : List ℕ) :
    (initialSmallCellList top cs).length + (initialSmallCellList top cs).length =
      scheduledSmallLength cs := by
  rw [initialSmallCellList_length, scheduledSmallLength_eq]
  omega

theorem scheduled_drop_length_balance (top : ℕ) (cs : List ℕ) (n : ℕ)
    (hn : n < cs.length) :
    4 + scheduledSmallLength (cs.drop (n + 1)) + 4 * n =
      (initialSmallCellList top cs).length + (initialSmallCellList top cs).length := by
  rw [scheduledSmallLength_eq, List.length_drop, initialSmallCellList_length]
  omega

theorem scheduled_selected_prior (A B : Set ℕ) (N : ℕ) (X : ℝ) (hi : ℕ)
    (D P : Finset ℕ) (Qb : Finset ℕ) (top : ℕ) (cs : List ℕ) (n m : ℕ)
    (hn : n < cs.length) :
    HEq (scheduledRegularPrior
      (fun j => primeSubsetPrior P (selectedTailCellPrimes A B N X hi D j))
      (primeSubsetPrior P Qb) top (cs.drop n) n m)
      (movingTemplateRestoredPrior n (scheduledSmallLength (cs.drop (n + 1))) m
          (selectedCompensationPrior A B N X hi D P cs n)
          (scheduledRegularPrior
            (fun j => primeSubsetPrior P (selectedTailCellPrimes A B N X hi D j))
            (primeSubsetPrior P Qb) top (cs.drop (n + 1)) n m)) := by
  unfold selectedCompensationPrior
  rw [drop_eq_headD_cons cs 0 n hn]
  simp only [List.headD_cons]
  exact heq_of_eq (scheduledRegularPrior_restore _ _ _ _ _ _ _)

end Ostmann

end OAI
