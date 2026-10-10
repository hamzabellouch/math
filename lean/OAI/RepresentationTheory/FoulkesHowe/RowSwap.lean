import Mathlib

namespace OAI

/-!
# From rowwise permutation invariance to individual slot swaps

The flattened plethysm forms are invariant under independent permutations
inside each row.  The polynomial derivative formulas instead ask for
invariance under a swap of two individual slots.  These lemmas provide that
conversion for any realization of symmetric powers.
-/

namespace Problem346

variable {α β V W : Type*}

/-- A transposition within one row acts by the transposition on that row
and by the identity on every other row. -/
theorem swap_same_row_apply [DecidableEq α] [DecidableEq β]
    (r : α) (j k : β) (p : α × β) :
    Equiv.swap (r, j) (r, k) p =
      (p.1, if p.1 = r then Equiv.swap j k p.2 else p.2) := by
  rcases p with ⟨i, l⟩
  by_cases hi : i = r
  · subst i
    by_cases hj : l = j
    · subst l
      simp
    by_cases hk : l = k
    · subst l
      simp
    · simp [Equiv.swap_apply_of_ne_of_ne, hj, hk]
  · have hj : (i, l) ≠ (r, j) := fun h => hi (congrArg Prod.fst h)
    have hk : (i, l) ≠ (r, k) := fun h => hi (congrArg Prod.fst h)
    simp [Equiv.swap_apply_of_ne_of_ne hj hk, hi]

/-- Independent rowwise permutation invariance implies invariance under a
swap of any two slots in a fixed row. -/
theorem rowwise_invariant_swap [DecidableEq α] [DecidableEq β]
    (F : (α × β → V) → W)
    (hF : ∀ (σ : α → Equiv.Perm β) (x : α × β → V),
      F (fun p => x (p.1, σ p.1 p.2)) = F x)
    (r : α) (j k : β) (x : α × β → V) :
    F (fun p => x (Equiv.swap (r, j) (r, k) p)) = F x := by
  have h := hF (fun i => if i = r then Equiv.swap j k else Equiv.refl β) x
  convert h using 1
  congr 1
  funext p
  rw [swap_same_row_apply]
  by_cases hp : p.1 = r <;> simp [hp]

/-- Coefficient-array version of the preceding lemma.  This is the swap
invariance hypothesis required by the grouped polynomial derivative rule. -/
theorem rowwise_coefficients_swap {κ : Type*}
    [DecidableEq α] [DecidableEq β]
    (F : (α × β → V) → W)
    (hF : ∀ (σ : α → Equiv.Perm β) (x : α × β → V),
      F (fun p => x (p.1, σ p.1 p.2)) = F x)
    (e : κ → V) (r : α) (j k : β) (c : α × β → κ) :
    F (fun p => e ((c ∘ Equiv.swap (r, j) (r, k)) p)) =
      F (fun p => e (c p)) := by
  exact rowwise_invariant_swap F hF r j k (fun p => e (c p))

end Problem346

end OAI
