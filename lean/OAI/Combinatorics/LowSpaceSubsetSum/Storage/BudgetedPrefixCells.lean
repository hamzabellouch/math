import OAI.Combinatorics.LowSpaceSubsetSum.Search.BudgetedPrefixController
import OAI.Combinatorics.LowSpaceSubsetSum.Storage.PreparedCollectCells
import OAI.Combinatorics.LowSpaceSubsetSum.Search.BudgetedParentCollector

namespace OAI

/-! # Live memory through the interrupted depth-first prefix traversal

An overflowing dictionary is released before descending. The suspended
frame retains the two bounded restriction lists, the order tail, and scalar
counters. Sequential children share a single working region.
-/

namespace LowSpaceSubsetSum.BudgetedPrefixCells

variable {n : ℕ} {I : Instance n} {C : ℕ}

abbrev Execution (α : Type*) := (Option (α × ℕ) × ℕ) × ℕ

def frame (n : ℕ) := 20 * (n + 1) ^ 2

def run
    (collect : StoredRestriction n → ℕ → Execution (StoredEntry.Dictionary I C))
    (check : Array (StoredEntry n) → ℕ → Execution Bool)
    (keep : StoredEntry.Dictionary I C → ℕ) :
    List (Fin n) → StoredRestriction n → ℕ → Execution Bool
  | order, P, budget =>
    if StoredPrefixController.header n ≤ budget then
      let task := collect P (budget - StoredPrefixController.header n)
      match task.1.1 with
      | none => ((none, task.1.2 + 2), frame n + task.2)
      | some (dictionary, available) =>
        if dictionary.val.keys.overflow then
          match order with
          | [] => ((some (false, available), task.1.2 + 4), frame n + task.2)
          | i :: rest =>
            let p₀ := P.force i false
            let left := run collect check keep rest p₀.1 available
            match left.1.1 with
            | none => ((none, task.1.2 + p₀.2 + left.1.2 + 6),
                frame n + max task.2 left.2)
            | some (true, remaining) =>
                ((some (true, remaining), task.1.2 + p₀.2 + left.1.2 + 6),
                  frame n + max task.2 left.2)
            | some (false, remaining) =>
                let p₁ := P.force i true
                let right := run collect check keep rest p₁.1 remaining
                ((right.1.1, task.1.2 + p₀.2 + left.1.2 + p₁.2 + right.1.2 + 8),
                  frame n + max task.2 (max left.2 right.2))
        else
          let checked := check dictionary.val.records available
          ((checked.1.1, task.1.2 + checked.1.2 + 4),
            frame n + max task.2 (keep dictionary + checked.2))
    else ((none, 1), frame n)

theorem value
    (collect : StoredRestriction n → ℕ → Execution (StoredEntry.Dictionary I C))
    (check : Array (StoredEntry n) → ℕ → Execution Bool)
    (keep : StoredEntry.Dictionary I C → ℕ)
    (order : List (Fin n)) (P : StoredRestriction n) (budget : ℕ) :
    (run collect check keep order P budget).1 =
      BudgetedPrefixController.run (fun p b => (collect p b).1)
        (fun a b => (check a b).1) order P budget := by
  induction order generalizing P budget with
  | nil =>
    rw [run, BudgetedPrefixController.run]
    dsimp only
    split
    · split
      · simp_all only
      · split <;> simp_all only [ite_true, Bool.false_eq_true, ite_false]
    · simp_all only
  | cons i order ih =>
    rw [run, BudgetedPrefixController.run]
    dsimp only
    split
    · split
      · simp_all only
      · split
        · simp only [← ih]
          split <;> simp_all only [ite_true]
        · simp_all only [Bool.false_eq_true, ite_false]
    · simp_all only

theorem cells
    (collect : StoredRestriction n → ℕ → Execution (StoredEntry.Dictionary I C))
    (check : Array (StoredEntry n) → ℕ → Execution Bool)
    (keep : StoredEntry.Dictionary I C → ℕ)
    (L R K : ℕ) (hcollect : ∀ p b, (collect p b).2 ≤ L)
    (hkeep : ∀ d, keep d ≤ R)
    (hcheck : ∀ (d : StoredEntry.Dictionary I C) b, (check d.val.records b).2 ≤ K)
    (order : List (Fin n)) (P : StoredRestriction n) (budget : ℕ) :
    (run collect check keep order P budget).2 ≤
      frame n * (order.length + 1) + L + R + K := by
  induction order generalizing P budget with
  | nil =>
    have ht := hcollect P (budget - StoredPrefixController.header n)
    rw [run]
    dsimp only
    simp only [List.length_nil, Nat.zero_add, Nat.mul_one]
    split
    · split
      · dsimp only; omega
      next d available h =>
        have hk := hkeep d
        have hc := hcheck d available
        split
        · dsimp only; omega
        · dsimp only
          have hm : max (collect P (budget - StoredPrefixController.header n)).2
              (keep d + (check d.val.records available).2) ≤ L+R+K := max_le (by omega) (by omega)
          omega
    · omega
  | cons i order ih =>
    have ht := hcollect P (budget - StoredPrefixController.header n)
    have hl := ih (P.force i false).1
    have hr := ih (P.force i true).1
    have hu : L ≤ frame n * (order.length + 1) + L + R + K := by omega
    rw [run]
    dsimp only
    simp only [List.length_cons]
    split
    · split
      · dsimp only; nlinarith only [ht, Nat.zero_le (frame n * order.length)]
      next d available h =>
        have hk := hkeep d
        have hc := hcheck d available
        split
        · split
          · dsimp only
            have hm := max_le (ht.trans hu) (hl available)
            nlinarith only [hm]
          · dsimp only
            have hm := max_le (ht.trans hu) (hl available)
            nlinarith only [hm]
          next remaining hleft =>
            dsimp only
            have hm := max_le (ht.trans hu) (max_le (hl available) (hr remaining))
            nlinarith only [hm]
        · dsimp only
          have hm : max (collect P (budget - StoredPrefixController.header n)).2
              (keep d + (check d.val.records available).2) ≤ L+R+K := max_le (by omega) (by omega)
          nlinarith only [hm, Nat.zero_le (frame n * order.length)]
    · nlinarith only [Nat.zero_le (frame n * order.length)]

def collect (D : RepresentationParentData n) (F : IndexedMask n)
    (hF : F.semantic = D.signs) (B : ℕ) (P : StoredRestriction n) (budget : ℕ) :
    Execution (StoredEntry.Dictionary D.input D.capacity) :=
  let out := PreparedCollectCells.run D F P hF B D.capacity budget
  ((out.1.1.map (fun (r, b) => (r.dictionary, b)), out.1.2), out.2)

theorem collect_value (D : RepresentationParentData n) (F : IndexedMask n)
    (hF : F.semantic = D.signs) (B : ℕ) (P : StoredRestriction n) (budget : ℕ) :
    (collect D F hF B P budget).1 = BudgetedParentCollector.collect D F hF B D.capacity P budget := by
  simp only [collect, PreparedCollectCells.run_value, BudgetedParentCollector.collect]

theorem collect_cells (D : RepresentationParentData n) (F : IndexedMask n)
    (hF : F.semantic = D.signs) (B : ℕ) (P : StoredRestriction n) (budget : ℕ)
    (hn : 10000 ≤ n) (hl : ∀ j, (D.pair j).left.occurrences.card ≤ D.capacity)
    (hr : ∀ j, (D.pair j).right.occurrences.card ≤ D.capacity)
    (hC : D.capacity ≤ 2 ^ n) (hB : B ≤ D.capacity) :
    (collect D F hF B P budget).2 ≤ inputScale D.input ^ 14 * (D.capacity + 1) :=
  PreparedCollectCells.run_cells D F P hF B budget hn hl hr hC hB

end LowSpaceSubsetSum.BudgetedPrefixCells

end OAI
