import OAI.Combinatorics.LowSpaceSubsetSum.Search.ExactFallback

namespace OAI

/-! # Linear live storage for the exact depth-first fallback -/

namespace LowSpaceSubsetSum.FallbackCells

variable {ι : Type*}

def run (a : ι → ℤ) : List ι → ℤ → (Bool × ℕ) × ℕ
  | [], target => ((decide (target = 0), 1), 8)
  | x :: xs, target =>
    let left := run a xs target
    if left.1.1 then ((true, left.1.2+1), left.2+8)
    else
      let right := run a xs (target-a x)
      ((right.1.1, left.1.2+right.1.2+1), max left.2 right.2+8)

theorem value (a : ι → ℤ) (xs : List ι) (target : ℤ) :
    (run a xs target).1 = ExactFallback.run a xs target := by
  induction xs generalizing target with
  | nil => rfl
  | cons x xs ih =>
    rw [run, ExactFallback.run]
    have hl := ih target
    have hr := ih (target-a x)
    rw [← hl, ← hr]
    split <;> rfl

theorem cells (a : ι → ℤ) (xs : List ι) (target : ℤ) :
    (run a xs target).2 ≤ 8*(xs.length+1) := by
  induction xs generalizing target with
  | nil => exact le_rfl
  | cons x xs ih =>
    have hl := ih target
    have hr := ih (target-a x)
    rw [run]
    split
    · dsimp only
      simp only [List.length_cons]
      omega
    · dsimp only
      have hm := max_le hl hr
      simp only [List.length_cons]
      omega

def decision {n : ℕ} (I : Instance n) : (Bool × ℕ) × ℕ :=
  let out := run (fun i => (I.values i : ℤ)) (List.finRange n) I.target
  (out.1, out.2+n+8)

theorem decision_value {n : ℕ} (I : Instance n) :
    (decision I).1.1 = ExactFallback.decision I := by
  exact congrArg Prod.fst (value (fun i => (I.values i : ℤ)) (List.finRange n) I.target)

theorem decision_cells {n : ℕ} (I : Instance n) : (decision I).2 ≤ 9*n+16 := by
  have h := cells (fun i => (I.values i : ℤ)) (List.finRange n) I.target
  rw [List.length_finRange] at h
  change _+n+8 ≤ _
  omega

end LowSpaceSubsetSum.FallbackCells

end OAI
