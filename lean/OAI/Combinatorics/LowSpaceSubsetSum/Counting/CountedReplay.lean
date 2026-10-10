import OAI.Combinatorics.LowSpaceSubsetSum.Streams.BufferReplay

namespace OAI

/-! # Cost-carrying tie-suffix replay

Every performed reader, key and callback evaluation contributes its own
counter. The result is exactly the bounded replay. The work bound
uses its actual stopped query/report counts, rather than the supplied fuel.
-/

namespace LowSpaceSubsetSum.CountedReplay

universe u v w
variable {α : Type u} {σ : Type v} {τ : Type w}

def runAcc (read : σ → Option (α × σ) × ℕ) (key : α → ℤ × ℕ) (K : ℤ)
    (report : α → τ → (τ × Bool) × ℕ) :
    ℕ → σ → τ → ℕ → ℕ → TieReplay.Result σ τ × ℕ
  | 0, s, a, q, r => (⟨s, a, q, r, false, false⟩, 1)
  | fuel + 1, s, a, q, r =>
    let fetched := read s
    match fetched.1 with
    | none => (⟨s, a, q + 1, r, true, false⟩, fetched.2 + 5)
    | some (x, s') =>
      let found := key x
      if found.1 = K then
        let emitted := report x a
        if emitted.1.2 then
          (⟨s', emitted.1.1, q + 1, r + 1, false, true⟩,
            fetched.2 + found.2 + emitted.2 + 8)
        else
          let rest := runAcc read key K report fuel s' emitted.1.1 (q + 1) (r + 1)
          (rest.1, fetched.2 + found.2 + emitted.2 + 8 + rest.2)
      else (⟨s, a, q + 1, r, true, false⟩, fetched.2 + found.2 + 6)

theorem runAcc_value (read : σ → Option (α × σ) × ℕ) (key : α → ℤ × ℕ) (K : ℤ)
    (report : α → τ → (τ × Bool) × ℕ) (fuel : ℕ) (s : σ) (a : τ) (q r : ℕ) :
    (runAcc read key K report fuel s a q r).1 =
      TieReplay.runAcc (fun s => (read s).1) (fun x => (key x).1) K
        (fun x a => (report x a).1) fuel s a q r := by
  induction fuel generalizing s a q r with
  | zero => rfl
  | succ fuel ih =>
    cases hr : (read s).1 with
    | none => simp only [runAcc, TieReplay.runAcc, hr]
    | some z =>
      rcases z with ⟨x, s'⟩
      simp only [runAcc, TieReplay.runAcc, hr]
      split
      · split
        · rfl
        · exact ih _ _ _ _
      · rfl

theorem runAcc_work (read : σ → Option (α × σ) × ℕ) (key : α → ℤ × ℕ) (K : ℤ)
    (report : α → τ → (τ × Bool) × ℕ) (R L C : ℕ)
    (hr : ∀ s, (read s).2 ≤ R) (hk : ∀ x, (key x).2 ≤ L)
    (hc : ∀ x a, (report x a).2 ≤ C)
    (fuel : ℕ) (s : σ) (a : τ) (q r : ℕ) :
    (runAcc read key K report fuel s a q r).2 + (R + L + 8) * q + C * r ≤
      (R + L + 8) * (runAcc read key K report fuel s a q r).1.queries +
        C * (runAcc read key K report fuel s a q r).1.reports + 1 := by
  induction fuel generalizing s a q r with
  | zero => simp only [runAcc]; omega
  | succ fuel ih =>
    have hread := hr s
    cases hv : (read s).1 with
    | none =>
      simp only [runAcc, hv, Nat.mul_add, Nat.mul_one]
      omega
    | some z =>
      rcases z with ⟨x, s'⟩
      have hkey := hk x
      simp only [runAcc, hv]
      split
      · have hcallback := hc x a
        split
        · simp only [Nat.mul_add, Nat.mul_one]; omega
        · have hrest := ih s' (report x a).1.1 (q + 1) (r + 1)
          simp only [Nat.mul_add, Nat.mul_one] at hrest
          dsimp only
          omega
      · simp only [Nat.mul_add, Nat.mul_one]; omega

def run (read : σ → Option (α × σ) × ℕ) (key : α → ℤ × ℕ) (K : ℤ)
    (report : α → τ → (τ × Bool) × ℕ) (fuel : ℕ) (s : σ) (a : τ) :
    TieReplay.Result σ τ × ℕ := runAcc read key K report fuel s a 0 0

theorem run_value (read : σ → Option (α × σ) × ℕ) (key : α → ℤ × ℕ) (K : ℤ)
    (report : α → τ → (τ × Bool) × ℕ) (fuel : ℕ) (s : σ) (a : τ) :
    (run read key K report fuel s a).1 =
      TieReplay.run (fun s => (read s).1) (fun x => (key x).1) K
        (fun x a => (report x a).1) fuel s a := runAcc_value _ _ _ _ _ _ _ _ _

theorem run_work (read : σ → Option (α × σ) × ℕ) (key : α → ℤ × ℕ) (K : ℤ)
    (report : α → τ → (τ × Bool) × ℕ) (R L C : ℕ)
    (hr : ∀ s, (read s).2 ≤ R) (hk : ∀ x, (key x).2 ≤ L)
    (hc : ∀ x a, (report x a).2 ≤ C) (fuel : ℕ) (s : σ) (a : τ) :
    (run read key K report fuel s a).2 ≤
      (R + L + 8) * (run read key K report fuel s a).1.queries +
        C * (run read key K report fuel s a).1.reports + 1 := by
  simpa only [run, Nat.mul_zero, Nat.add_zero] using
    runAcc_work read key K report R L C hr hk hc fuel s a 0 0

end LowSpaceSubsetSum.CountedReplay

end OAI
