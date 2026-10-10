import OAI.Combinatorics.LowSpaceSubsetSum.Streams.BufferReplay

namespace OAI

/-!
# Reporting one item's matches against a buffered tie group

The immutable prefix buffer is reused. A generator suffix is restored only
when the group was longer than the buffer. The callback may stop in either
part; its work and stream queries are bounded on every outcome.
-/

namespace LowSpaceSubsetSum
namespace JoinOne

universe u v w

variable {α : Type u} {σ : Type v} {τ : Type w}

def run (read : σ → Option (α × σ)) (key : α → ℤ) (K : ℤ)
    (report : α → τ → τ × Bool) (buffer : Array α) (saved : σ)
    (long : Bool) (fuel : ℕ) (a : τ) : TieReplay.Result σ τ :=
  let first := BufferReplay.run key K report buffer a
  if first.halted then
    ⟨saved, first.state, first.queries, first.reports, false, true⟩
  else if long then
    let rest := TieReplay.run read key K report fuel saved first.state
    ⟨rest.cursor, rest.state, first.queries + rest.queries,
      first.reports + rest.reports, rest.complete, rest.halted⟩
  else ⟨saved, first.state, first.queries, first.reports, true, false⟩

theorem reports_le (read : σ → Option (α × σ)) (key : α → ℤ) (K : ℤ)
    (report : α → τ → τ × Bool) (view : σ → List α) (hread : RowMerge.IsReader read view)
    (buffer : Array α) (saved : σ) (long : Bool) (fuel : ℕ) (a : τ) :
    (run read key K report buffer saved long fuel a).reports ≤
      buffer.size + (TieBuffer.groupView key K view saved).length := by
  have hb := BufferReplay.reports_le key K report buffer a
  dsimp only [run]
  split
  · exact hb.trans (Nat.le_add_right _ _)
  · split
    · have hr := TieReplay.run_reports_le_potential read key K report view hread
        fuel saved (BufferReplay.run key K report buffer a).state
      exact Nat.add_le_add hb hr
    · exact hb.trans (Nat.le_add_right _ _)

theorem queries_le (read : σ → Option (α × σ)) (key : α → ℤ) (K : ℤ)
    (report : α → τ → τ × Bool) (view : σ → List α) (hread : RowMerge.IsReader read view)
    (buffer : Array α) (saved : σ) (long : Bool) (fuel : ℕ) (a : τ) :
    (run read key K report buffer saved long fuel a).queries ≤
      buffer.size + (TieBuffer.groupView key K view saved).length + 1 := by
  have hb := BufferReplay.queries_le key K report buffer a
  dsimp only [run]
  split
  · dsimp only
    omega
  · split
    · have hr := TieReplay.run_queries_le_potential read key K report view hread
        fuel saved (BufferReplay.run key K report buffer a).state
      dsimp only
      omega
    · dsimp only
      omega

theorem halted_false (read : σ → Option (α × σ)) (key : α → ℤ) (K : ℤ)
    (report : α → τ → τ × Bool) (hreport : ∀ x a, (report x a).2 = false)
    (buffer : Array α) (saved : σ) (long : Bool) (fuel : ℕ) (a : τ) :
    (run read key K report buffer saved long fuel a).halted = false := by
  have hb : (BufferReplay.run key K report buffer a).halted = false :=
    TieReplay.run_halted_false _ _ _ _ hreport _ _ _
  simp only [run, hb, Bool.false_eq_true, ite_false]
  split
  · exact TieReplay.run_halted_false _ _ _ _ hreport _ _ _
  · rfl

/-- Completed reporting is precisely prefix reporting followed by suffix
reporting; a short group has no suffix to restore. -/
theorem state_complete (read : σ → Option (α × σ)) (key : α → ℤ) (K : ℤ)
    (report : α → τ → τ × Bool) (hreport : ∀ x a, (report x a).2 = false)
    (view : σ → List α) (hread : RowMerge.IsReader read view)
    (buffer : Array α) (hkeys : ∀ x ∈ buffer.toList, key x = K)
    (saved : σ) (fuel : ℕ) (a : τ)
    (hfuel : (TieBuffer.groupView key K view saved).length ≤ fuel) :
    (run read key K report buffer saved (TieBuffer.hasKey read key K saved) fuel a).state =
      (buffer.toList ++ TieBuffer.groupView key K view saved).foldl
        (fun a x => (report x a).1) a := by
  have hb : (BufferReplay.run key K report buffer a).halted = false :=
    TieReplay.run_halted_false _ _ _ _ hreport _ _ _
  have hs := BufferReplay.state_complete key K report hreport buffer a hkeys
  simp only [run, hb, Bool.false_eq_true, ite_false]
  by_cases hl : TieBuffer.hasKey read key K saved = true
  · simp only [hl, ite_true]
    rw [TieReplay.run_state_complete read key K report hreport view hread fuel saved _ hfuel,
      hs, List.foldl_append]
  · have he : TieBuffer.groupView key K view saved = [] := by
      by_contra he
      exact hl ((TieBuffer.hasKey_iff read key K view hread saved).mpr he)
    have hfalse : TieBuffer.hasKey read key K saved = false := Bool.eq_false_iff.mpr hl
    simp only [hfalse, Bool.false_eq_true, ite_false, he, List.append_nil]
    exact hs

theorem suffix_empty (read : σ → Option (α × σ)) (key : α → ℤ) (K : ℤ)
    (report : α → τ → τ × Bool) (hreport : ∀ x a, (report x a).2 = false)
    (view : σ → List α) (hread : RowMerge.IsReader read view)
    (buffer : Array α) (saved : σ) (fuel : ℕ) (a : τ)
    (hfuel : (TieBuffer.groupView key K view saved).length ≤ fuel) :
    TieBuffer.groupView key K view
      (run read key K report buffer saved (TieBuffer.hasKey read key K saved) fuel a).cursor = [] := by
  have hb : (BufferReplay.run key K report buffer a).halted = false :=
    TieReplay.run_halted_false _ _ _ _ hreport _ _ _
  simp only [run, hb, Bool.false_eq_true, ite_false]
  by_cases hl : TieBuffer.hasKey read key K saved = true
  · simp only [hl, ite_true]
    have h := (TieReplay.runAcc_nonhalting_spec read key K report hreport view hread
      fuel saved (BufferReplay.run key K report buffer a).state 0 0).2.2.1
    exact h.trans (List.drop_eq_nil_of_le hfuel)
  · simp only [Bool.eq_false_iff.mpr hl, Bool.false_eq_true, ite_false]
    by_contra he
    exact hl ((TieBuffer.hasKey_iff read key K view hread saved).mpr he)

theorem view_complete (read : σ → Option (α × σ)) (key : α → ℤ) (K : ℤ)
    (report : α → τ → τ × Bool) (hreport : ∀ x a, (report x a).2 = false)
    (view : σ → List α) (hread : RowMerge.IsReader read view)
    (buffer : Array α) (saved : σ) (fuel : ℕ) (a : τ)
    (hfuel : (TieBuffer.groupView key K view saved).length ≤ fuel) :
    view saved = TieBuffer.groupView key K view saved ++
      view (run read key K report buffer saved (TieBuffer.hasKey read key K saved) fuel a).cursor := by
  have hb : (BufferReplay.run key K report buffer a).halted = false :=
    TieReplay.run_halted_false _ _ _ _ hreport _ _ _
  simp only [run, hb, Bool.false_eq_true, ite_false]
  by_cases hl : TieBuffer.hasKey read key K saved = true
  · simp only [hl, ite_true]
    have h := (TieReplay.runAcc_nonhalting_spec read key K report hreport view hread
      fuel saved (BufferReplay.run key K report buffer a).state 0 0).2.2.2
    simpa only [TieReplay.run, List.take_of_length_le hfuel] using h
  · have he : TieBuffer.groupView key K view saved = [] := by
      by_contra he
      exact hl ((TieBuffer.hasKey_iff read key K view hread saved).mpr he)
    simp only [Bool.eq_false_iff.mpr hl, Bool.false_eq_true, ite_false, he, List.nil_append]

def runFilled (read : σ → Option (α × σ)) (key : α → ℤ) (K : ℤ)
    (report : α → τ → τ × Bool) (B fuel : ℕ) (s : σ) (a : τ) : TieReplay.Result σ τ :=
  let filled := TieBuffer.fill read key K B s
  run read key K report filled.buffer filled.cursor
    (TieBuffer.hasKey read key K filled.cursor) fuel a

theorem filled_reports_le (read : σ → Option (α × σ)) (key : α → ℤ) (K : ℤ)
    (report : α → τ → τ × Bool) (view : σ → List α) (hread : RowMerge.IsReader read view)
    (B fuel : ℕ) (s : σ) (a : τ) :
    (runFilled read key K report B fuel s a).reports ≤
      (TieBuffer.groupView key K view s).length := by
  have h := reports_le read key K report view hread (TieBuffer.fill read key K B s).buffer
    (TieBuffer.fill read key K B s).cursor
    (TieBuffer.hasKey read key K (TieBuffer.fill read key K B s).cursor) fuel a
  have hb := congrArg List.length (TieBuffer.fill_buffer read key K view hread B s)
  rw [TieBuffer.fill_suffix read key K view hread B s] at h
  simp only [Array.length_toList, List.length_take] at hb
  simp only [List.length_drop] at h
  dsimp only [runFilled]
  omega

theorem filled_queries_le (read : σ → Option (α × σ)) (key : α → ℤ) (K : ℤ)
    (report : α → τ → τ × Bool) (view : σ → List α) (hread : RowMerge.IsReader read view)
    (B fuel : ℕ) (s : σ) (a : τ) :
    (runFilled read key K report B fuel s a).queries ≤
      (TieBuffer.groupView key K view s).length + 1 := by
  have h := queries_le read key K report view hread (TieBuffer.fill read key K B s).buffer
    (TieBuffer.fill read key K B s).cursor
    (TieBuffer.hasKey read key K (TieBuffer.fill read key K B s).cursor) fuel a
  have hb := congrArg List.length (TieBuffer.fill_buffer read key K view hread B s)
  rw [TieBuffer.fill_suffix read key K view hread B s] at h
  simp only [Array.length_toList, List.length_take] at hb
  simp only [List.length_drop] at h
  dsimp only [runFilled]
  omega

theorem filled_state_complete (read : σ → Option (α × σ)) (key : α → ℤ) (K : ℤ)
    (report : α → τ → τ × Bool) (hreport : ∀ x a, (report x a).2 = false)
    (view : σ → List α) (hread : RowMerge.IsReader read view)
    (B fuel : ℕ) (s : σ) (a : τ)
    (hfuel : (TieBuffer.groupView key K view s).length ≤ fuel) :
    (runFilled read key K report B fuel s a).state =
      (TieBuffer.groupView key K view s).foldl (fun a x => (report x a).1) a := by
  have hf : (TieBuffer.groupView key K view (TieBuffer.fill read key K B s).cursor).length ≤
      fuel := by
    rw [TieBuffer.fill_suffix read key K view hread B s, List.length_drop]
    omega
  have h := state_complete read key K report hreport view hread
    (TieBuffer.fill read key K B s).buffer
    (BufferReplay.filled_buffer_keys read key K view hread B s)
    (TieBuffer.fill read key K B s).cursor fuel a hf
  rw [TieBuffer.fill_buffer read key K view hread B s,
    TieBuffer.fill_suffix read key K view hread B s, List.take_append_drop] at h
  exact h

theorem filled_view_complete (read : σ → Option (α × σ)) (key : α → ℤ) (K : ℤ)
    (report : α → τ → τ × Bool) (hreport : ∀ x a, (report x a).2 = false)
    (view : σ → List α) (hread : RowMerge.IsReader read view)
    (B fuel : ℕ) (s : σ) (a : τ)
    (hfuel : (TieBuffer.groupView key K view s).length ≤ fuel) :
    view s = TieBuffer.groupView key K view s ++
      view (runFilled read key K report B fuel s a).cursor := by
  have hf : (TieBuffer.groupView key K view (TieBuffer.fill read key K B s).cursor).length ≤
      fuel := by
    rw [TieBuffer.fill_suffix read key K view hread B s, List.length_drop]
    omega
  have hs := view_complete read key K report hreport view hread
    (TieBuffer.fill read key K B s).buffer (TieBuffer.fill read key K B s).cursor fuel a hf
  have h := (TieBuffer.fillAcc_spec read key K view hread B s #[] 0).2.1
  change view s = (TieBuffer.groupView key K view s).take B ++
    view (TieBuffer.fill read key K B s).cursor at h
  rw [hs, TieBuffer.fill_suffix read key K view hread B s, ← List.append_assoc,
    List.take_append_drop] at h
  exact h

end JoinOne
end LowSpaceSubsetSum

end OAI
