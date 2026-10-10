import OAI.Combinatorics.LowSpaceSubsetSum.Counting.CountedReplay
import OAI.Combinatorics.LowSpaceSubsetSum.Streams.JoinOne

namespace OAI

/-! # Counted buffered and suffix replay for one matching occurrence

A suffix restore invokes the supplied concrete cloning procedure. Its cost
is charged only on the long-group branch. Query and report counters continue
to denote the exact stopped execution.
-/

namespace LowSpaceSubsetSum.CountedJoinOne

universe u v w
variable {α : Type u} {σ : Type v} {τ : Type w}

def run (read : σ → Option (α × σ) × ℕ) (key : α → ℤ × ℕ) (K : ℤ)
    (report : α → τ → (τ × Bool) × ℕ) (clone : σ → σ × ℕ)
    (buffer : Array α) (saved : σ) (long : Bool) (fuel : ℕ) (a : τ) :
    TieReplay.Result σ τ × ℕ :=
  let first := CountedReplay.run (fun i => (BufferReplay.read buffer i, 4)) key K report buffer.size 0 a
  if first.1.halted then
    (⟨saved, first.1.state, first.1.queries, first.1.reports, false, true⟩, first.2 + 4)
  else if long then
    let copied := clone saved
    let rest := CountedReplay.run read key K report fuel copied.1 first.1.state
    (⟨rest.1.cursor, rest.1.state, first.1.queries + rest.1.queries,
      first.1.reports + rest.1.reports, rest.1.complete, rest.1.halted⟩,
      first.2 + copied.2 + rest.2 + 5)
  else (⟨saved, first.1.state, first.1.queries, first.1.reports, true, false⟩, first.2 + 4)

theorem run_value (read : σ → Option (α × σ) × ℕ) (key : α → ℤ × ℕ) (K : ℤ)
    (report : α → τ → (τ × Bool) × ℕ) (clone : σ → σ × ℕ)
    (hclone : ∀ s, (clone s).1 = s)
    (buffer : Array α) (saved : σ) (long : Bool) (fuel : ℕ) (a : τ) :
    (run read key K report clone buffer saved long fuel a).1 =
      JoinOne.run (fun s => (read s).1) (fun x => (key x).1) K
        (fun x a => (report x a).1) buffer saved long fuel a := by
  simp only [run, CountedReplay.run_value, hclone, JoinOne.run, BufferReplay.run]
  split
  · simp_all only [↓reduceIte]
  · simp_all only
    split <;> rfl

theorem run_work (read : σ → Option (α × σ) × ℕ) (key : α → ℤ × ℕ) (K : ℤ)
    (report : α → τ → (τ × Bool) × ℕ) (clone : σ → σ × ℕ)
    (R L C B : ℕ) (hr : ∀ s, (read s).2 ≤ R) (hk : ∀ x, (key x).2 ≤ L)
    (hc : ∀ x a, (report x a).2 ≤ C) (hcopy : ∀ s, (clone s).2 ≤ B)
    (buffer : Array α) (saved : σ) (long : Bool) (fuel : ℕ) (a : τ) :
    (run read key K report clone buffer saved long fuel a).2 ≤
      (max R 4 + L + 8) * (run read key K report clone buffer saved long fuel a).1.queries +
        C * (run read key K report clone buffer saved long fuel a).1.reports +
          (if long then B else 0) + 7 := by
  let first := CountedReplay.run (fun i => (BufferReplay.read buffer i, 4)) key K report buffer.size 0 a
  have hf0 := CountedReplay.run_work (fun i => (BufferReplay.read buffer i, 4)) key K report
    4 L C (fun _ => le_rfl) hk hc buffer.size 0 a
  have hf : first.2 ≤ (max R 4 + L + 8) * first.1.queries + C * first.1.reports + 1 := by
    change first.2 ≤ (4 + L + 8) * first.1.queries + C * first.1.reports + 1 at hf0
    have hmul := Nat.mul_le_mul_right first.1.queries
      (show 4 + L + 8 ≤ max R 4 + L + 8 by omega)
    exact hf0.trans (by omega)
  have hfirst : CountedReplay.run (fun i => (BufferReplay.read buffer i, 4)) key K report
      buffer.size 0 a = first := rfl
  simp only [run, hfirst]
  by_cases hh : first.1.halted = true
  · simp only [hh, ↓reduceIte]
    change first.2 + 4 ≤ (max R 4 + L + 8) * first.1.queries + C * first.1.reports + _ + 7
    omega
  · have hfalse : first.1.halted = false := Bool.eq_false_iff.mpr hh
    by_cases hl : long = true
    · let rest := CountedReplay.run read key K report fuel (clone saved).1 first.1.state
      have hr0 := CountedReplay.run_work read key K report R L C hr hk hc fuel (clone saved).1 first.1.state
      have hrest : rest.2 ≤ (max R 4 + L + 8) * rest.1.queries + C * rest.1.reports + 1 := by
        change rest.2 ≤ (R + L + 8) * rest.1.queries + C * rest.1.reports + 1 at hr0
        have hmul := Nat.mul_le_mul_right rest.1.queries
          (show R + L + 8 ≤ max R 4 + L + 8 by omega)
        exact hr0.trans (by omega)
      have hcp := hcopy saved
      simp only [hfalse, Bool.false_eq_true, hl, ↓reduceIte]
      change first.2 + (clone saved).2 + rest.2 + 5 ≤
        (max R 4 + L + 8) * (first.1.queries + rest.1.queries) +
          C * (first.1.reports + rest.1.reports) + B + 7
      simp only [Nat.mul_add]
      omega
    · have hlfalse : long = false := Bool.eq_false_iff.mpr hl
      simp only [hfalse, hlfalse, Bool.false_eq_true, ↓reduceIte]
      change first.2 + 4 ≤ (max R 4 + L + 8) * first.1.queries + C * first.1.reports + 0 + 7
      omega

end LowSpaceSubsetSum.CountedJoinOne

end OAI
