import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternBulkData
import OAI.NumberTheory.Ostmann.Arithmetic.MovingUnitSampleBound
import OAI.NumberTheory.Ostmann.Construction.WordTransferFullPeriod

namespace OAI

/-! # Concrete length and frequency budgets for the original pattern pair -/

namespace Ostmann
open scoped Classical

theorem movingLeafLengthLE_map {A B : Type*} (f : A → B) (n : ℕ)
    (x : TreeLeafTuple (List A) n) (r : ℕ) (hx : MovingLeafLengthLE n x r) :
    MovingLeafLengthLE n (treeLeafMap (List.map f) n x) r := by
  induction n with
  | zero => simpa only [MovingLeafLengthLE, treeLeafMap, List.length_map] using hx
  | succ n ih => exact ⟨ih x.1 hx.1, ih x.2 hx.2⟩

theorem bulkSlotLeaves_length {A : Type*} (n m : ℕ)
    (slot : TreeLeafIndex n × Fin m → A) :
    MovingLeafLengthLE n (bulkSlotLeaves n m slot) m := by
  induction n with
  | zero => simp [bulkSlotLeaves, MovingLeafLengthLE, treeLeafTupleEquiv]
  | succ n ih =>
    change MovingLeafLengthLE n
      (bulkSlotLeaves n m (fun j => slot (.inl j.1, j.2))) m ∧
      MovingLeafLengthLE n (bulkSlotLeaves n m (fun j => slot (.inr j.1, j.2))) m
    exact ⟨ih _, ih _⟩

theorem movingPatternFinBulkData_size {B C : Type*} {N n m r : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (t : Bool → FrequencyTree ℤ n)
    (small : Bool → TreeLeafTuple (List B) n) (slot : (TreeLeafIndex n × Fin m) ↪ B)
    (perm : Equiv.Perm (TreeLeafIndex n × Fin m))
    (pattern : Bool × MovingSampleIndex n → C)
    (hsmall : ∀ b, MovingLeafLengthLE n (small b) r) (b : Bool) :
    (movingPatternFinBulkData e n m t small slot perm pattern b).SizeLE
      (2 ^ n * (r + m + 4 * n + 4)) := by
  rw [movingPatternFinBulkData_build]
  apply buildMovingSlotData_size n (t b) _ _ _ r m
    (movingLeafLengthLE_map _ n (small b) r (hsmall b))
  cases b <;> exact bulkSlotLeaves_length n m _

theorem movingPatternFinBulkData_regular_length {B C : Type*} {N n m r : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (t : Bool → FrequencyTree ℤ n)
    (small : Bool → TreeLeafTuple (List B) n) (slot : (TreeLeafIndex n × Fin m) ↪ B)
    (perm : Equiv.Perm (TreeLeafIndex n × Fin m))
    (pattern : Bool × MovingSampleIndex n → C)
    (hsmall : ∀ b, MovingLeafLengthLE n (small b) r) (b : Bool) :
    (movingPatternFinBulkData e n m t small slot perm pattern b).RegularLengthLE
      (2 ^ n * (r + m + 4 * n)) := by
  rw [movingPatternFinBulkData_build]
  apply buildMovingSlotData_regular_length n (t b) _ _ _ r m
    (movingLeafLengthLE_map _ n (small b) r (hsmall b))
  cases b <;> exact bulkSlotLeaves_length n m _

theorem movingPatternFinBulkData_follows {B C : Type*} {N n m : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (t : Bool → FrequencyTree ℤ n)
    (small : Bool → TreeLeafTuple (List B) n) (slot : (TreeLeafIndex n × Fin m) ↪ B)
    (perm : Equiv.Perm (TreeLeafIndex n × Fin m))
    (pattern : Bool × MovingSampleIndex n → C) (b : Bool) :
    (movingPatternFinBulkData e n m t small slot perm pattern b).Follows (t b) := by
  rw [movingPatternFinBulkData_build]
  exact buildMovingSlotData_follows _ _ _ _ _

/-- The literal frequency list controls every actual formula-node frequency. -/
theorem MovingSlotData.Follows.frequencies_iff {A : Type*} {n : ℕ}
    {T : MovingSlotData A n} {t : FrequencyTree ℤ n} (h : T.Follows t) (P : ℤ → Prop) :
    T.Frequencies P ↔ ∀ s ∈ allFrequencyList n t, P s := by
  induction T with
  | leaf s L =>
    change s = t at h
    subst s
    simp only [MovingSlotData.Frequencies, allFrequencyList, List.mem_singleton, forall_eq]
  | node s CL CR u l r hl hr =>
    rcases h with ⟨hs, hL, hR⟩
    simp only [MovingSlotData.Frequencies, hs, allFrequencyList,
      List.mem_cons, List.mem_append, or_imp, forall_and, forall_eq,
      hl hL, hr hR]

/-- Frequency bounds are taken from the original histories, not from an
additional assumption on each pattern realization. -/
theorem movingPatternFinBulkData_frequencies {B C : Type*} {N n m : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (t : Bool → FrequencyTree ℤ n)
    (small : Bool → TreeLeafTuple (List B) n) (slot : (TreeLeafIndex n × Fin m) ↪ B)
    (perm : Equiv.Perm (TreeLeafIndex n × Fin m))
    (pattern : Bool × MovingSampleIndex n → C) (P : ℤ → Prop)
    (hP : ∀ b, ∀ s ∈ allFrequencyList n (t b), P s) (b : Bool) :
    (movingPatternFinBulkData e n m t small slot perm pattern b).Frequencies P :=
  ((movingPatternFinBulkData_follows e t small slot perm pattern b).frequencies_iff P).mpr (hP b)

end Ostmann

end OAI
