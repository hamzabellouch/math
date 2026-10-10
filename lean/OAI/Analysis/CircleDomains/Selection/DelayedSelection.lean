import OAI.Analysis.CircleDomains.Selection.OrderedSelectionSlots

namespace OAI

/-! Reserve the first coordinate slot for the zero test while preserving
all selected tests and their order. -/

open Set Function

namespace CircleDomainRigidity

def delayedSelection {C : Type*} (A : ℕ → Set C) : ℕ → Set C
  | 0 => ∅
  | n + 1 => A n

theorem delayedSelection_mono {C : Type*} (A : ℕ → Set C) (hA : Monotone A) :
    Monotone (delayedSelection A) := by
  apply monotone_nat_of_le_succ
  intro n
  cases n with
  | zero => exact empty_subset _
  | succ n => exact hA (Nat.le_succ n)

theorem delayedSelection_single {C : Type*} (A : ℕ → Set C) (hzero : A 0 = ∅)
    (hA : ∀ n, (A (n + 1) \ A n).Subsingleton) (n : ℕ) :
    (delayedSelection A (n + 1) \ delayedSelection A n).Subsingleton := by
  cases n with
  | zero => simp [delayedSelection, hzero]
  | succ n => exact hA n

theorem iUnion_delayedSelection {C : Type*} (A : ℕ → Set C) :
    (⋃ n, delayedSelection A n) = ⋃ n, A n := by
  ext x
  constructor
  · intro hx
    obtain ⟨n, hn⟩ := mem_iUnion.mp hx
    cases n with
    | zero => exact hn.elim
    | succ n => exact mem_iUnion.mpr ⟨n, hn⟩
  · intro hx
    obtain ⟨n, hn⟩ := mem_iUnion.mp hx
    exact mem_iUnion.mpr ⟨n + 1, hn⟩

end CircleDomainRigidity

end OAI
