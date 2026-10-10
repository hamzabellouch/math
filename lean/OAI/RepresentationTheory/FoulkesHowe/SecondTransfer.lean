import OAI.RepresentationTheory.FoulkesHowe.EncodedCancellation
import OAI.RepresentationTheory.FoulkesHowe.SecondCounts
import OAI.RepresentationTheory.FoulkesHowe.SecondSwap
import OAI.RepresentationTheory.FoulkesHowe.SecondEndpoints
import OAI.RepresentationTheory.FoulkesHowe.GridCancellation

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem346.SecondTransfer

universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V]

/-- Polynomial encoding preserves the independent factor permutations of each row. -/
theorem polynomial_row_permute {κ : Type*} [Fintype κ] {r b : ℕ}
    (T : SymmetricMultilinearForm (r+1) b V) (e : κ → V)
    (l : Fin (r+1) × Fin b → Block r)
    (σ : Fin (r+1) → Equiv.Perm (Fin b)) :
    multilinearPolynomial (flattenedSymmetricForm T) e
        (fun p => l (p.1, σ p.1 p.2)) =
      multilinearPolynomial (flattenedSymmetricForm T) e l := by
  apply MvPolynomial.funext
  intro z
  simp only [eval_multilinearPolynomial]
  exact flattenedSymmetricForm_inner_permute T σ
    (fun p => ∑ j : κ, z (l p,j) • e j)

/-- A single unfinished row can be recovered from its one-step progressed state. -/
theorem polynomial_step {κ : Type*} [Fintype κ] {r b : ℕ}
    (T : SymmetricMultilinearForm (r+1) b V) (e : κ → V)
    (hb : r * (r+1) ≤ b) (k : Fin r → ℕ) (hk : ∀ j, k j ≤ r)
    (i : Fin r) (hi : k i < r)
    (hnext : multilinearPolynomial (flattenedSymmetricForm T) e
      (label (Function.update k i (k i+1))) = 0) :
    multilinearPolynomial (flattenedSymmetricForm T) e (label k) = 0 := by
  classical
  apply multilinearPolynomial_eq_zero_of_replacements
    (flattenedSymmetricForm T) e (label k) (some i.succ) none (by simp)
  · have hd := destination_occurrences_lt_source (b := b) k hb hk i hi
    simpa only [Finset.card_filter] using hd
  · rintro ⟨row,j⟩ hp
    obtain ⟨hrow,hj⟩ := (label_eq_source_iff k i (row,j)).mp hp
    change row = i.succ at hrow
    change k i ≤ j.val at hj
    subst row
    have hrb : r ≤ b := by nlinarith
    have hki : k i < b := lt_of_lt_of_le hi hrb
    have heq := invariant_update_label_eq_progress
      (fun l => multilinearPolynomial (flattenedSymmetricForm T) e l)
      (polynomial_row_permute T e) k i hki j hj
    exact heq.trans hnext

/-- The second differential transfer: remove the common degree-`r` power from
all `r` moving arguments. Count-vector induction allows the shifts in any order. -/
theorem second_transfer [FiniteDimensional ℂ V] (r m : ℕ)
    (hb : r * (r+1) ≤ r+m)
    (T : SymmetricMultilinearForm (r+1) (r+m) V)
    (h : ∀ x t : V, ∀ Q : Fin r → SymPow m V,
      T (Fin.cons (symMonomial (r+m) V (fun _ => t))
        (fun i => symPowMul r m (symMonomial r V (fun _ => x)) (Q i))) = 0) :
    ∀ v : Fin (r+1) → V,
      T (fun i => symMonomial (r+m) V (fun _ => v i)) = 0 := by
  classical
  let e := Module.finBasis ℂ V
  let P (k : Fin r → ℕ) :=
    multilinearPolynomial (flattenedSymmetricForm T) e (label k)
  have hend : P (fun _ => r) = 0 := terminal_polynomial_zero r m T e h
  have hzero : P (fun _ => 0) = 0 := by
    apply zero_of_upward_grid r P hend
    · intro k hk i hi hnext
      exact polynomial_step T e hb k hk i hi hnext
    · intro i
      exact Nat.zero_le r
  exact independent_powers_zero_of_initial_polynomial_zero T e hzero

end Problem346.SecondTransfer

end

end OAI
