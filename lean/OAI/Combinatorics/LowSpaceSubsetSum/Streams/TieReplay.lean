import OAI.Combinatorics.LowSpaceSubsetSum.Streams.TieBuffer

namespace OAI

/-!
# Bounded replay of one tie suffix

The reporter can stop after any matching occurrence. The replay retains
only its cursor, callback state, counters, and fixed key. Its recursion is
tail recursion. All attempted reports are bounded by the complete suffix
length, even if the callback or fuel stops execution early.
-/

namespace LowSpaceSubsetSum
namespace TieReplay

universe u v w

variable {α : Type u} {σ : Type v} {τ : Type w}

structure Result (σ : Type v) (τ : Type w) where
  cursor : σ
  state : τ
  queries : ℕ
  reports : ℕ
  complete : Bool
  halted : Bool

def runAcc (read : σ → Option (α × σ)) (key : α → ℤ) (K : ℤ)
    (report : α → τ → τ × Bool) : ℕ → σ → τ → ℕ → ℕ → Result σ τ
  | 0, s, a, q, r => ⟨s, a, q, r, false, false⟩
  | fuel + 1, s, a, q, r => match read s with
    | none => ⟨s, a, q + 1, r, true, false⟩
    | some (x, s') => if key x = K then
        let out := report x a
        if out.2 then ⟨s', out.1, q + 1, r + 1, false, true⟩
        else runAcc read key K report fuel s' out.1 (q + 1) (r + 1)
      else ⟨s, a, q + 1, r, true, false⟩

def run (read : σ → Option (α × σ)) (key : α → ℤ) (K : ℤ)
    (report : α → τ → τ × Bool) (fuel : ℕ) (s : σ) (a : τ) : Result σ τ :=
  runAcc read key K report fuel s a 0 0

theorem runAcc_bounds (read : σ → Option (α × σ)) (key : α → ℤ) (K : ℤ)
    (report : α → τ → τ × Bool) (view : σ → List α) (hread : RowMerge.IsReader read view)
    (fuel : ℕ) (s : σ) (a : τ) (q r : ℕ) :
    (runAcc read key K report fuel s a q r).queries ≤ q + fuel ∧
    r ≤ (runAcc read key K report fuel s a q r).reports ∧
    (runAcc read key K report fuel s a q r).reports ≤
      r + min fuel (TieBuffer.groupView key K view s).length := by
  induction fuel generalizing s a q r with
  | zero => simp [runAcc]
  | succ fuel ih =>
    have hr := hread s
    cases h : read s with
    | none =>
      simp only [h] at hr
      simp [runAcc, h, TieBuffer.groupView, hr]
    | some z =>
      rcases z with ⟨x, s'⟩
      simp only [h] at hr
      by_cases hx : key x = K
      · have hg : TieBuffer.groupView key K view s =
            x :: TieBuffer.groupView key K view s' := by
          simp [TieBuffer.groupView, hr, hx]
        simp only [runAcc, h, ite_eq_left hx]
        split
        · simp only [hg, List.length_cons]
          omega
        · have hi := ih s' (report x a).1 (q + 1) (r + 1)
          simp only [hg, List.length_cons]
          omega
      · have hg : TieBuffer.groupView key K view s = [] := by
          simp [TieBuffer.groupView, hr, hx]
        simp [runAcc, h, hx, hg]

theorem run_queries_le (read : σ → Option (α × σ)) (key : α → ℤ) (K : ℤ)
    (report : α → τ → τ × Bool) (view : σ → List α) (hread : RowMerge.IsReader read view)
    (fuel : ℕ) (s : σ) (a : τ) : (run read key K report fuel s a).queries ≤ fuel := by
  simpa [run] using (runAcc_bounds read key K report view hread fuel s a 0 0).1

theorem run_reports_le_potential (read : σ → Option (α × σ)) (key : α → ℤ) (K : ℤ)
    (report : α → τ → τ × Bool) (view : σ → List α) (hread : RowMerge.IsReader read view)
    (fuel : ℕ) (s : σ) (a : τ) :
    (run read key K report fuel s a).reports ≤ (TieBuffer.groupView key K view s).length := by
  have h := (runAcc_bounds read key K report view hread fuel s a 0 0).2.2
  simp only [run, zero_add] at h ⊢
  exact h.trans (Nat.min_le_right _ _)

/-- The one final lookahead is the only read not charged to a reportable
occurrence, even when the fuel is much larger than the tie group. -/
theorem runAcc_queries_le_potential (read : σ → Option (α × σ)) (key : α → ℤ) (K : ℤ)
    (report : α → τ → τ × Bool) (view : σ → List α) (hread : RowMerge.IsReader read view)
    (fuel : ℕ) (s : σ) (a : τ) (q r : ℕ) :
    (runAcc read key K report fuel s a q r).queries ≤
      q + min fuel ((TieBuffer.groupView key K view s).length + 1) := by
  induction fuel generalizing s a q r with
  | zero => simp [runAcc]
  | succ fuel ih =>
    have hr := hread s
    cases h : read s with
    | none =>
      simp only [h] at hr
      simp [runAcc, h, TieBuffer.groupView, hr]
    | some z =>
      rcases z with ⟨x, s'⟩
      simp only [h] at hr
      by_cases hx : key x = K
      · have hg : TieBuffer.groupView key K view s =
            x :: TieBuffer.groupView key K view s' := by
          simp [TieBuffer.groupView, hr, hx]
        simp only [runAcc, h, ite_eq_left hx, hg, List.length_cons]
        split
        · dsimp only
          omega
        · have hi := ih s' (report x a).1 (q + 1) (r + 1)
          omega
      · have hg : TieBuffer.groupView key K view s = [] := by
          simp [TieBuffer.groupView, hr, hx]
        simp [runAcc, h, hx, hg]

theorem run_queries_le_potential (read : σ → Option (α × σ)) (key : α → ℤ) (K : ℤ)
    (report : α → τ → τ × Bool) (view : σ → List α) (hread : RowMerge.IsReader read view)
    (fuel : ℕ) (s : σ) (a : τ) :
    (run read key K report fuel s a).queries ≤ (TieBuffer.groupView key K view s).length + 1 := by
  have h := runAcc_queries_le_potential read key K report view hread fuel s a 0 0
  simp only [run, zero_add] at h ⊢
  exact h.trans (Nat.min_le_right _ _)

theorem runAcc_halted_false (read : σ → Option (α × σ)) (key : α → ℤ) (K : ℤ)
    (report : α → τ → τ × Bool) (hreport : ∀ x a, (report x a).2 = false)
    (fuel : ℕ) (s : σ) (a : τ) (q r : ℕ) :
    (runAcc read key K report fuel s a q r).halted = false := by
  induction fuel generalizing s a q r with
  | zero => rfl
  | succ fuel ih =>
    cases h : read s with
    | none => simp [runAcc, h]
    | some z =>
      rcases z with ⟨x, s'⟩
      by_cases hx : key x = K
      · simp only [runAcc, h, ite_eq_left hx, hreport, Bool.false_eq_true, ite_false]
        exact ih _ _ _ _
      · simp [runAcc, h, hx]

theorem run_halted_false (read : σ → Option (α × σ)) (key : α → ℤ) (K : ℤ)
    (report : α → τ → τ × Bool) (hreport : ∀ x a, (report x a).2 = false)
    (fuel : ℕ) (s : σ) (a : τ) :
    (run read key K report fuel s a).halted = false :=
  runAcc_halted_false read key K report hreport fuel s a 0 0

/-- A callback invariant can depend on the exact number of reports. This
also applies to executions stopped by the callback or by the fuel. -/
theorem runAcc_preserves (read : σ → Option (α × σ)) (key : α → ℤ) (K : ℤ)
    (report : α → τ → τ × Bool) (P : τ → ℕ → Prop)
    (hstep : ∀ x a r, P a r → P (report x a).1 (r + 1))
    (fuel : ℕ) (s : σ) (a : τ) (q r : ℕ) (ha : P a r) :
    P (runAcc read key K report fuel s a q r).state
      (runAcc read key K report fuel s a q r).reports := by
  induction fuel generalizing s a q r with
  | zero => exact ha
  | succ fuel ih =>
    cases h : read s with
    | none => simpa only [runAcc, h] using ha
    | some z =>
      rcases z with ⟨x, s'⟩
      by_cases hx : key x = K
      · simp only [runAcc, h, ite_eq_left hx]
        split
        · exact hstep x a r ha
        · exact ih s' (report x a).1 (q + 1) (r + 1) (hstep x a r ha)
      · simpa only [runAcc, h, ite_eq_right hx] using ha

theorem run_preserves (read : σ → Option (α × σ)) (key : α → ℤ) (K : ℤ)
    (report : α → τ → τ × Bool) (P : τ → ℕ → Prop)
    (hstep : ∀ x a r, P a r → P (report x a).1 (r + 1))
    (fuel : ℕ) (s : σ) (a : τ) (ha : P a 0) :
    P (run read key K report fuel s a).state (run read key K report fuel s a).reports :=
  runAcc_preserves read key K report P hstep fuel s a 0 0 ha

/-- If reporting continues, replay processes exactly the requested prefix
of the tie suffix and leaves every following occurrence untouched. -/
theorem runAcc_nonhalting_spec (read : σ → Option (α × σ)) (key : α → ℤ) (K : ℤ)
    (report : α → τ → τ × Bool) (hreport : ∀ x a, (report x a).2 = false)
    (view : σ → List α) (hread : RowMerge.IsReader read view)
    (fuel : ℕ) (s : σ) (a : τ) (q r : ℕ) :
    (runAcc read key K report fuel s a q r).state =
      ((TieBuffer.groupView key K view s).take fuel).foldl (fun a x => (report x a).1) a ∧
    (runAcc read key K report fuel s a q r).reports =
      r + min fuel (TieBuffer.groupView key K view s).length ∧
    TieBuffer.groupView key K view (runAcc read key K report fuel s a q r).cursor =
      (TieBuffer.groupView key K view s).drop fuel ∧
    view s = (TieBuffer.groupView key K view s).take fuel ++
      view (runAcc read key K report fuel s a q r).cursor := by
  induction fuel generalizing s a q r with
  | zero => simp [runAcc]
  | succ fuel ih =>
    have hr := hread s
    cases h : read s with
    | none =>
      simp only [h] at hr
      simp [runAcc, h, TieBuffer.groupView, hr]
    | some z =>
      rcases z with ⟨x, s'⟩
      simp only [h] at hr
      by_cases hx : key x = K
      · have hg : TieBuffer.groupView key K view s =
            x :: TieBuffer.groupView key K view s' := by
          simp [TieBuffer.groupView, hr, hx]
        have hi := ih s' (report x a).1 (q + 1) (r + 1)
        simp only [runAcc, h, ite_eq_left hx, hreport, Bool.false_eq_true, ite_false]
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [hi.1, hg]
          simp
        · rw [hi.2.1, hg]
          simp only [List.length_cons]
          omega
        · rw [hi.2.2.1, hg]
          simp
        · rw [hr, hi.2.2.2, hg]
          simp
      · have hg : TieBuffer.groupView key K view s = [] := by
          simp [TieBuffer.groupView, hr, hx]
        simp [runAcc, h, hx, hg]

theorem run_state_complete (read : σ → Option (α × σ)) (key : α → ℤ) (K : ℤ)
    (report : α → τ → τ × Bool) (hreport : ∀ x a, (report x a).2 = false)
    (view : σ → List α) (hread : RowMerge.IsReader read view)
    (fuel : ℕ) (s : σ) (a : τ)
    (hfuel : (TieBuffer.groupView key K view s).length ≤ fuel) :
    (run read key K report fuel s a).state =
      (TieBuffer.groupView key K view s).foldl (fun a x => (report x a).1) a := by
  have h := (runAcc_nonhalting_spec read key K report hreport view hread fuel s a 0 0).1
  simpa [run, List.take_of_length_le hfuel] using h

end TieReplay
end LowSpaceSubsetSum

end OAI
