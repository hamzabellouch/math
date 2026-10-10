import OAI.Combinatorics.LowSpaceSubsetSum.Storage.StoredPrefixFilter

namespace OAI

/-! # Tail filtering with explicit accumulator and reversal cells -/

namespace LowSpaceSubsetSum.MeasuredFilterCells

variable {α : Type*}

/-- The live peak is a proof-side execution annotation. The value and work
projection performs exactly the tail filter. -/
def runAcc (test : α → (Bool × ℕ) × ℕ) :
    List α → List α → ℕ → ℕ → (List α × ℕ) × ℕ
  | [], acc, work, peak => ((acc.reverse, work + acc.length + 1), max peak (2 * acc.length + 4))
  | x :: xs, acc, work, peak =>
    let p := test x
    runAcc test xs (if p.1.1 then x :: acc else acc) (work + p.1.2 + 3)
      (max peak (2 * (xs.length + acc.length + 1) + p.2 + 4))

theorem runAcc_value (test : α → (Bool × ℕ) × ℕ) (xs acc : List α) (work peak : ℕ) :
    (runAcc test xs acc work peak).1 =
      MeasuredFilter.runAcc (fun x => (test x).1) xs acc work := by
  induction xs generalizing acc work peak with
  | nil => rfl
  | cons x xs ih => simp only [runAcc, MeasuredFilter.runAcc, ih]

theorem runAcc_cells (test : α → (Bool × ℕ) × ℕ) (H : ℕ)
    (ht : ∀ x, (test x).2 ≤ H) (xs acc : List α) (work peak : ℕ) :
    (runAcc test xs acc work peak).2 ≤
      max peak (2 * (xs.length + acc.length) + H + 4) := by
  induction xs generalizing acc work peak with
  | nil =>
    simp only [runAcc, List.length_nil, Nat.zero_add]
    exact max_le_max le_rfl (by omega)
  | cons x xs ih =>
    have hx := ht x
    simp only [runAcc]
    cases hb : (test x).1.1
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have h := ih acc (work + (test x).1.2 + 3)
        (max peak (2 * (xs.length + acc.length + 1) + (test x).2 + 4))
      simp only [List.length_cons] at h ⊢
      omega
    · simp only [↓reduceIte]
      have h := ih (x :: acc) (work + (test x).1.2 + 3)
        (max peak (2 * (xs.length + acc.length + 1) + (test x).2 + 4))
      simp only [List.length_cons] at h ⊢
      omega

def run (test : α → (Bool × ℕ) × ℕ) (xs : List α) : (List α × ℕ) × ℕ :=
  runAcc test xs [] 0 0

theorem run_value (test : α → (Bool × ℕ) × ℕ) (xs : List α) :
    (run test xs).1 = MeasuredFilter.runAcc (fun x => (test x).1) xs [] 0 :=
  runAcc_value test xs [] 0 0

theorem run_cells (test : α → (Bool × ℕ) × ℕ) (H : ℕ)
    (ht : ∀ x, (test x).2 ≤ H) (xs : List α) :
    (run test xs).2 ≤ 2 * xs.length + H + 4 := by
  simpa only [run, List.length_nil, Nat.add_zero, Nat.zero_max] using
    runAcc_cells test H ht xs [] 0 0

theorem run_length (test : α → (Bool × ℕ) × ℕ) (xs : List α) :
    (run test xs).1.1.length ≤ xs.length := by
  rw [run_value, MeasuredFilter.runAcc_value]
  simpa only [List.reverse_nil, List.nil_append] using
    List.length_filter_le (fun x => (test x).1.1) xs

end LowSpaceSubsetSum.MeasuredFilterCells

end OAI
