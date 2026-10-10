import OAI.Combinatorics.LowSpaceSubsetSum.Separators.BudgetedSeparatorArrays
import OAI.Combinatorics.LowSpaceSubsetSum.Separators.PreparedSeparatorContext

namespace OAI

/-! # The budgeted checker for retained dictionary arrays

The preparation expression in the proofs identifies an already-built
context. Execution receives its block list and both retained arrays;
it does not recompute the context for an individual right dictionary.
-/

namespace LowSpaceSubsetSum.BudgetedPreparedSeparator

open StoredSeparatorCheck

variable {n g : ℕ}

theorem reference_value (C : TopCoordinates n g)
    (rows : Fin 4 → Vector (Fin n) g) (hrows : ∀ i j, (rows i)[j] = C.index (i, j))
    (families : Fin 4 → Array (Fin (2 ^ g)))
    (hsize : ∀ i, (families i).size ≤ 11 * 2 ^ g)
    (capacity : ℕ) (hcap : capacity = 2 ^ n) (target : ℤ)
    (left right : Array (StoredEntry n)) :
    (BudgetedSeparatorCheck.reference capacity target
      (PreparedSeparatorContext.prepare rows families hsize).1 left.toList right.toList).1 =
      (C.check (fun i => (families i).map SeparatorStoredMasks.decode) target
        (left.toList.map StoredEntry.semantic) (right.toList.map StoredEntry.semantic)).accepted := by
  rw [BudgetedSeparatorCheck.reference_value capacity hcap target,
    PreparedSeparatorContext.prepare_value,
    PreparedSeparatorRefinement.source_result C rows hrows]

theorem allowance (I : Instance n) (hn : 10000 ≤ n) (hg : g ≤ n)
    (C : TopCoordinates n g)
    (rows : Fin 4 → Vector (Fin n) g) (hrows : ∀ i j, (rows i)[j] = C.index (i, j))
    (families : Fin 4 → Array (Fin (2 ^ g)))
    (hsize : ∀ i, (families i).size ≤ 11 * 2 ^ g)
    (capacity : ℕ) (hcap : capacity = 2 ^ n) (target : ℤ)
    (left right : Array (StoredEntry n)) :
    BudgetedSeparatorArrays.allowance capacity target
      (PreparedSeparatorContext.prepare rows families hsize).1 left right ≤
      inputScale I ^ 6 *
        ((C.check (fun i => (families i).map SeparatorStoredMasks.decode) target
          (left.toList.map StoredEntry.semantic) (right.toList.map StoredEntry.semantic)).scans +
          left.size + right.size + 1) := by
  have hlen : (PreparedSeparatorContext.prepare rows families hsize).1.length = 4 := by
    rw [PreparedSeparatorContext.prepare_value]
    exact prepareFour_length _ _ _ _ _ _
  have hsteps : ∀ b ∈ (PreparedSeparatorContext.prepare rows families hsize).1,
      b.steps ≤ n + 4 := by
    rw [PreparedSeparatorContext.prepare_value]
    exact PreparedSeparatorWork.prepared_steps _ _ _ _ _ _ (fun _ => by omega)
  have h := BudgetedSeparatorArrays.allowance_scale I hn capacity hcap target
    (PreparedSeparatorContext.prepare rows families hsize).1 hlen hg hsteps left right
  rw [PreparedSeparatorContext.prepare_value,
    PreparedSeparatorRefinement.source_result C rows hrows] at h
  exact h

theorem value (C : TopCoordinates n g)
    (rows : Fin 4 → Vector (Fin n) g) (hrows : ∀ i j, (rows i)[j] = C.index (i, j))
    (families : Fin 4 → Array (Fin (2 ^ g)))
    (hsize : ∀ i, (families i).size ≤ 11 * 2 ^ g)
    (capacity : ℕ) (hcap : capacity = 2 ^ n) (target : ℤ)
    (left right : Array (StoredEntry n)) (budget : ℕ) (result : Bool) (remaining : ℕ)
    (h : (BudgetedSeparatorArrays.execute capacity target
      (PreparedSeparatorContext.prepare rows families hsize).1 left right budget).1 =
      some (result, remaining)) :
    result = (C.check (fun i => (families i).map SeparatorStoredMasks.decode) target
      (left.toList.map StoredEntry.semantic) (right.toList.map StoredEntry.semantic)).accepted := by
  have hv := BudgetedSeparatorArrays.value capacity hcap target
    (PreparedSeparatorContext.prepare rows families hsize).1 left right budget result remaining h
  rw [PreparedSeparatorContext.prepare_value,
    PreparedSeparatorRefinement.source_result C rows hrows] at hv
  exact hv

theorem remaining_bound (I : Instance n) (hn : 10000 ≤ n) (hg : g ≤ n)
    (C : TopCoordinates n g)
    (rows : Fin 4 → Vector (Fin n) g) (hrows : ∀ i j, (rows i)[j] = C.index (i, j))
    (families : Fin 4 → Array (Fin (2 ^ g)))
    (hsize : ∀ i, (families i).size ≤ 11 * 2 ^ g)
    (capacity : ℕ) (hcap : capacity = 2 ^ n) (target : ℤ)
    (left right : Array (StoredEntry n)) (budget : ℕ) (result : Bool) (remaining : ℕ)
    (h : (BudgetedSeparatorArrays.execute capacity target
      (PreparedSeparatorContext.prepare rows families hsize).1 left right budget).1 =
      some (result, remaining)) :
    budget ≤ remaining + inputScale I ^ 6 *
      ((C.check (fun i => (families i).map SeparatorStoredMasks.decode) target
        (left.toList.map StoredEntry.semantic) (right.toList.map StoredEntry.semantic)).scans +
        left.size + right.size + 1) := by
  rw [BudgetedSeparatorArrays.remaining capacity target
    (PreparedSeparatorContext.prepare rows families hsize).1 left right budget result remaining h]
  exact Nat.add_le_add_left
    (allowance I hn hg C rows hrows families hsize capacity hcap target left right) remaining


theorem accepts (I : Instance n) (hn : 10000 ≤ n) (hg : g ≤ n)
    (C : TopCoordinates n g)
    (rows : Fin 4 → Vector (Fin n) g) (hrows : ∀ i j, (rows i)[j] = C.index (i, j))
    (families : Fin 4 → Array (Fin (2 ^ g)))
    (hsize : ∀ i, (families i).size ≤ 11 * 2 ^ g)
    (capacity : ℕ) (hcap : capacity = 2 ^ n) (target : ℤ)
    (left right : Array (StoredEntry n)) (budget : ℕ)
    (hbudget : inputScale I ^ 6 *
      ((C.check (fun i => (families i).map SeparatorStoredMasks.decode) target
        (left.toList.map StoredEntry.semantic) (right.toList.map StoredEntry.semantic)).scans +
        left.size + right.size + 1) ≤ budget)
    (hyes : (C.check (fun i => (families i).map SeparatorStoredMasks.decode) target
      (left.toList.map StoredEntry.semantic) (right.toList.map StoredEntry.semantic)).accepted = true) :
    ∃ remaining, (BudgetedSeparatorArrays.execute capacity target
      (PreparedSeparatorContext.prepare rows families hsize).1 left right budget).1 =
      some (true, remaining) := by
  have h := BudgetedSeparatorArrays.complete capacity target
    (PreparedSeparatorContext.prepare rows families hsize).1 left right budget
    ((allowance I hn hg C rows hrows families hsize capacity hcap target left right).trans hbudget)
  rw [reference_value C rows hrows families hsize capacity hcap target left right, hyes] at h
  exact ⟨_, h⟩

end LowSpaceSubsetSum.BudgetedPreparedSeparator

end OAI
