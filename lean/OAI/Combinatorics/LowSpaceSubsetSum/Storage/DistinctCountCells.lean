import OAI.Combinatorics.LowSpaceSubsetSum.Streams.MeasuredDistinctCount

namespace OAI

/-! # Live storage of the tail distinct-key counter

Each iteration drops the previous reader state after obtaining its
successor. The trace retains the previous scalar key, count, remaining
fuel and work counter, but no list of emitted values.
-/

namespace LowSpaceSubsetSum.DistinctCountCells

variable {α σ : Type*}

def loop (cells : σ → ℕ) (X : ℕ)
    (read : σ → (Option (α × σ) × ℕ) × ℕ) (key : α → (ℤ × ℕ) × ℕ) :
    ℕ → σ → Option ℤ → ℕ → ℕ → ℕ → (ℕ × ℕ) × ℕ
  | 0, s, _, count, work, peak => ((count, work+1), max peak (cells s+16))
  | fuel+1, s, previous, count, work, peak =>
    let out := read s
    match out.1.1 with
    | none => ((count, work+out.1.2+1), max peak (cells s+out.2+16))
    | some (x, next) =>
      let k := key x
      let fresh := match previous with | none => true | some p => decide (p ≠ k.1.1)
      loop cells X read key fuel next (some k.1.1) (count+if fresh then 1 else 0)
        (work+out.1.2+k.1.2+3)
        (max peak (cells s+cells next+out.2+k.2+X+32))

theorem loop_value (cells : σ → ℕ) (X : ℕ)
    (read : σ → (Option (α × σ) × ℕ) × ℕ) (key : α → (ℤ × ℕ) × ℕ)
    (fuel : ℕ) (s : σ) (previous : Option ℤ) (count work peak : ℕ) :
    (loop cells X read key fuel s previous count work peak).1 =
      MeasuredDistinctCount.loop (fun s => (read s).1) (fun x => (key x).1)
        fuel s previous count work := by
  induction fuel generalizing s previous count work peak with
  | zero => rfl
  | succ fuel ih =>
    cases h : (read s).1.1 with
    | none => simp only [loop, MeasuredDistinctCount.loop, h]
    | some out =>
      rcases out with ⟨x, next⟩
      simp only [loop, MeasuredDistinctCount.loop, h, ih]
      rfl

theorem loop_cells (cells : σ → ℕ) (X S R K : ℕ)
    (read : σ → (Option (α × σ) × ℕ) × ℕ) (key : α → (ℤ × ℕ) × ℕ)
    (hs : ∀ s, cells s ≤ S) (hr : ∀ s, (read s).2 ≤ R) (hk : ∀ x, (key x).2 ≤ K)
    (fuel : ℕ) (s : σ) (previous : Option ℤ) (count work peak : ℕ) :
    (loop cells X read key fuel s previous count work peak).2 ≤
      max peak (2*S+R+K+X+32) := by
  induction fuel generalizing s previous count work peak with
  | zero =>
    have h := hs s
    simp only [loop]
    exact max_le_max le_rfl (by omega)
  | succ fuel ih =>
    have h₀ := hs s
    have h₁ := hr s
    simp only [loop]
    split
    · dsimp only
      exact max_le_max le_rfl (by omega)
    next x next _ =>
      have h₂ := hs next
      have h₃ := hk x
      have h := ih next (some (key x).1.1)
        (count+if (match previous with | none => true | some p => decide (p ≠ (key x).1.1)) then 1 else 0)
        (work+(read s).1.2+(key x).1.2+3)
        (max peak (cells s+cells next+(read s).2+(key x).2+X+32))
      exact h.trans (by omega)

def run (cells : σ → ℕ) (X : ℕ)
    (read : σ → (Option (α × σ) × ℕ) × ℕ) (key : α → (ℤ × ℕ) × ℕ)
    (fuel : ℕ) (s : σ) : (ℕ × ℕ) × ℕ :=
  loop cells X read key fuel s none 0 0 0

theorem run_value (cells : σ → ℕ) (X : ℕ)
    (read : σ → (Option (α × σ) × ℕ) × ℕ) (key : α → (ℤ × ℕ) × ℕ)
    (fuel : ℕ) (s : σ) :
    (run cells X read key fuel s).1 =
      MeasuredDistinctCount.run (fun s => (read s).1) (fun x => (key x).1) fuel s :=
  loop_value cells X read key fuel s none 0 0 0

theorem run_cells (cells : σ → ℕ) (X S R K : ℕ)
    (read : σ → (Option (α × σ) × ℕ) × ℕ) (key : α → (ℤ × ℕ) × ℕ)
    (hs : ∀ s, cells s ≤ S) (hr : ∀ s, (read s).2 ≤ R) (hk : ∀ x, (key x).2 ≤ K)
    (fuel : ℕ) (s : σ) :
    (run cells X read key fuel s).2 ≤ 2*S+R+K+X+32 := by
  simpa only [run, Nat.zero_max] using loop_cells cells X S R K read key hs hr hk fuel s none 0 0 0

end LowSpaceSubsetSum.DistinctCountCells

end OAI
