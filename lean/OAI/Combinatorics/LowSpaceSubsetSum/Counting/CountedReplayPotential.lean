import OAI.Combinatorics.LowSpaceSubsetSum.Counting.CountedReplay

namespace OAI

/-! # Telescoping callback costs through a stopped replay

The callback may itself contain a replay. A potential on its returned state
charges that actual inner work; a uniform worst-case inner fuel bound is not
multiplied by the outer stream length.
-/

namespace LowSpaceSubsetSum.CountedReplay

universe u v w
variable {α : Type u} {σ : Type v} {τ : Type w}

theorem runAcc_work_potential
    (read : σ → Option (α × σ) × ℕ) (key : α → ℤ × ℕ) (K : ℤ)
    (report : α → τ → (τ × Bool) × ℕ) (potential : τ → ℕ) (R L C : ℕ)
    (hr : ∀ s, (read s).2 ≤ R) (hk : ∀ x, (key x).2 ≤ L)
    (hc : ∀ x a, (report x a).2 + potential a ≤ potential (report x a).1.1 + C)
    (fuel : ℕ) (s : σ) (a : τ) (q r : ℕ) :
    (runAcc read key K report fuel s a q r).2 + (R + L + C + 8) * q + potential a ≤
      (R + L + C + 8) * (runAcc read key K report fuel s a q r).1.queries +
        potential (runAcc read key K report fuel s a q r).1.state + 1 := by
  induction fuel generalizing s a q r with
  | zero => simp only [runAcc]; omega
  | succ fuel ih =>
    have hread := hr s
    cases hv : (read s).1 with
    | none => simp only [runAcc, hv, Nat.mul_add, Nat.mul_one]; omega
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

theorem run_work_potential
    (read : σ → Option (α × σ) × ℕ) (key : α → ℤ × ℕ) (K : ℤ)
    (report : α → τ → (τ × Bool) × ℕ) (potential : τ → ℕ) (R L C : ℕ)
    (hr : ∀ s, (read s).2 ≤ R) (hk : ∀ x, (key x).2 ≤ L)
    (hc : ∀ x a, (report x a).2 + potential a ≤ potential (report x a).1.1 + C)
    (fuel : ℕ) (s : σ) (a : τ) :
    (run read key K report fuel s a).2 + potential a ≤
      (R + L + C + 8) * (run read key K report fuel s a).1.queries +
        potential (run read key K report fuel s a).1.state + 1 := by
  simpa only [run, Nat.mul_zero, Nat.add_zero, Nat.zero_add] using
    runAcc_work_potential read key K report potential R L C hr hk hc fuel s a 0 0

end LowSpaceSubsetSum.CountedReplay

end OAI
