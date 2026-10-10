import OAI.Combinatorics.LowSpaceSubsetSum.Streams.DistinctStreamCount

namespace OAI

/-! # Tail-recursive distinct counting with measured reader calls

Only the current reader state, previous key, count, remaining fuel and work
counter survive each iteration. No list of emitted keys is constructed.
-/

namespace LowSpaceSubsetSum.MeasuredDistinctCount

variable {α σ : Type*}

def loop (read : σ → Option (α × σ) × ℕ) (key : α → ℤ × ℕ) :
    ℕ → σ → Option ℤ → ℕ → ℕ → ℕ × ℕ
  | 0, _, _, count, work => (count, work + 1)
  | fuel + 1, state, previous, count, work =>
    let out := read state
    match out.1 with
    | none => (count, work + out.2 + 1)
    | some (x, next) =>
      let k := key x
      let fresh := match previous with | none => true | some p => decide (p ≠ k.1)
      loop read key fuel next (some k.1) (count + if fresh then 1 else 0)
        (work + out.2 + k.2 + 3)

theorem loop_value (read : σ → Option (α × σ) × ℕ) (key : α → ℤ × ℕ)
    (fuel : ℕ) (s : σ) (previous : Option ℤ) (count work : ℕ) :
    (loop read key fuel s previous count work).1 = count +
      match previous with
      | none => (DistinctStreamCount.run (fun s => (read s).1) (fun x => (key x).1) fuel s).1
      | some p => (DistinctStreamCount.tail (fun s => (read s).1) (fun x => (key x).1) fuel s p).1 := by
  induction fuel generalizing s previous count work with
  | zero => cases previous <;> simp only [loop, DistinctStreamCount.run, DistinctStreamCount.tail, Nat.add_zero]
  | succ fuel ih =>
    cases previous with
    | none =>
      cases hr : (read s).1 with
      | none => simp only [loop, hr, DistinctStreamCount.run, Nat.add_zero]
      | some out =>
        rcases out with ⟨x, next⟩
        simp only [loop, hr, ↓reduceIte, ih, DistinctStreamCount.run]
        omega
    | some p =>
      cases hr : (read s).1 with
      | none => simp only [loop, hr, DistinctStreamCount.tail, Nat.add_zero]
      | some out =>
        rcases out with ⟨x, next⟩
        by_cases he : p = (key x).1
        · subst p
          simp only [loop, hr, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true,
            ↓reduceIte, Nat.add_zero, ih, DistinctStreamCount.tail]
        · simp only [loop, hr, ne_eq, he, not_false_eq_true, decide_true, ↓reduceIte,
            ih, DistinctStreamCount.tail]
          omega

theorem loop_work (read : σ → Option (α × σ) × ℕ) (key : α → ℤ × ℕ)
    (R K : ℕ) (hread : ∀ s, (read s).2 ≤ R) (hkey : ∀ x, (key x).2 ≤ K)
    (fuel : ℕ) (s : σ) (previous : Option ℤ) (count work : ℕ) :
    (loop read key fuel s previous count work).2 ≤ work + (R + K + 4) * fuel + 1 := by
  induction fuel generalizing s previous count work with
  | zero => simp only [loop, Nat.mul_zero, Nat.add_zero, le_refl]
  | succ fuel ih =>
    have hr := hread s
    simp only [loop]
    split
    · dsimp only
      nlinarith only [hr, Nat.zero_le ((R + K + 4) * fuel)]
    next x next _ =>
      have hk := hkey x
      have ht := ih next (some (key x).1)
        (count + if (match previous with | none => true | some p => decide (p ≠ (key x).1))
          then 1 else 0) (work + (read s).2 + (key x).2 + 3)
      nlinarith only [hr, hk, ht]

def run (read : σ → Option (α × σ) × ℕ) (key : α → ℤ × ℕ) (fuel : ℕ) (s : σ) : ℕ × ℕ :=
  loop read key fuel s none 0 0

theorem run_value (read : σ → Option (α × σ) × ℕ) (key : α → ℤ × ℕ) (fuel : ℕ) (s : σ) :
    (run read key fuel s).1 =
      (DistinctStreamCount.run (fun s => (read s).1) (fun x => (key x).1) fuel s).1 := by
  simpa only [run, Nat.zero_add] using loop_value read key fuel s none 0 0

theorem run_work (read : σ → Option (α × σ) × ℕ) (key : α → ℤ × ℕ)
    (R K : ℕ) (hread : ∀ s, (read s).2 ≤ R) (hkey : ∀ x, (key x).2 ≤ K)
    (fuel : ℕ) (s : σ) :
    (run read key fuel s).2 ≤ (R + K + 4) * fuel + 1 := by
  simpa only [run, Nat.zero_add] using loop_work read key R K hread hkey fuel s none 0 0

end LowSpaceSubsetSum.MeasuredDistinctCount

end OAI
