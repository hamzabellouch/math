import OAI.Combinatorics.LowSpaceSubsetSum.Streams.JoinOne

namespace OAI

/-!
# A stopped Cartesian tie-group join

A single second-stream prefix buffer and optional suffix snapshot serve every
first-stream occurrence with this key. Counters charge every attempted report,
including executions halted inside either part of a replay. Lists occur only
in the correctness specification.
-/

namespace LowSpaceSubsetSum
namespace TieGroup

universe u v s t w

variable {α : Type u} {β : Type v} {σ₁ : Type s} {σ₂ : Type t} {τ : Type w}

structure State (σ₂ : Type t) (τ : Type w) where
  last : σ₂
  user : τ
  queries : ℕ
  reports : ℕ
  restores : ℕ

def step (read₂ : σ₂ → Option (β × σ₂)) (key₂ : β → ℤ) (K : ℤ)
    (report : α → β → τ → τ × Bool) (buffer : Array β) (saved : σ₂)
    (long : Bool) (fuel₂ : ℕ) (x : α) (a : State σ₂ τ) : State σ₂ τ × Bool :=
  let out := JoinOne.run read₂ key₂ K (report x) buffer saved long fuel₂ a.user
  (⟨out.cursor, out.state, a.queries + out.queries, a.reports + out.reports,
    a.restores + if long then 1 else 0⟩, out.halted)

structure Result (σ₁ : Type s) (σ₂ : Type t) (τ : Type w) where
  outer : TieReplay.Result σ₁ (State σ₂ τ)
  fillQueries : ℕ
  bufferSize : ℕ
  snapshot : Bool

def run (read₁ : σ₁ → Option (α × σ₁)) (key₁ : α → ℤ)
    (read₂ : σ₂ → Option (β × σ₂)) (key₂ : β → ℤ) (K : ℤ)
    (report : α → β → τ → τ × Bool) (B fuel₁ fuel₂ : ℕ)
    (s₁ : σ₁) (s₂ : σ₂) (a : τ) : Result σ₁ σ₂ τ :=
  let filled := TieBuffer.fill read₂ key₂ K B s₂
  let long := TieBuffer.hasKey read₂ key₂ K filled.cursor
  let out := TieReplay.run read₁ key₁ K
    (step read₂ key₂ K report filled.buffer filled.cursor long fuel₂)
    fuel₁ s₁ ⟨filled.cursor, a, 0, 0, 0⟩
  ⟨out, filled.queries, filled.buffer.size, long && TieBuffer.hasKey read₁ key₁ K s₁⟩

/-- Bounds on callbacks follow from the actual suffix reporter, not from
assumed trial or implementation bounds. -/
theorem step_bounds (read₂ : σ₂ → Option (β × σ₂)) (key₂ : β → ℤ) (K : ℤ)
    (report : α → β → τ → τ × Bool) (view₂ : σ₂ → List β)
    (hread₂ : RowMerge.IsReader read₂ view₂) (buffer : Array β) (saved : σ₂)
    (long : Bool) (fuel₂ : ℕ) (x : α) (a : State σ₂ τ) :
    (step read₂ key₂ K report buffer saved long fuel₂ x a).1.reports ≤
        a.reports + (buffer.size + (TieBuffer.groupView key₂ K view₂ saved).length) ∧
    (step read₂ key₂ K report buffer saved long fuel₂ x a).1.queries ≤
        a.queries + (buffer.size + (TieBuffer.groupView key₂ K view₂ saved).length + 1) ∧
    (step read₂ key₂ K report buffer saved long fuel₂ x a).1.restores ≤ a.restores + 1 := by
  have hr := JoinOne.reports_le read₂ key₂ K (report x) view₂ hread₂ buffer saved long fuel₂ a.user
  have hq := JoinOne.queries_le read₂ key₂ K (report x) view₂ hread₂ buffer saved long fuel₂ a.user
  dsimp only [step]
  refine ⟨Nat.add_le_add_left hr _, Nat.add_le_add_left hq _, ?_⟩
  split <;> omega

theorem run_bounds (read₁ : σ₁ → Option (α × σ₁)) (key₁ : α → ℤ)
    (read₂ : σ₂ → Option (β × σ₂)) (key₂ : β → ℤ) (K : ℤ)
    (report : α → β → τ → τ × Bool)
    (view₁ : σ₁ → List α) (hread₁ : RowMerge.IsReader read₁ view₁)
    (view₂ : σ₂ → List β) (hread₂ : RowMerge.IsReader read₂ view₂)
    (B fuel₁ fuel₂ : ℕ) (s₁ : σ₁) (s₂ : σ₂) (a : τ) :
    (run read₁ key₁ read₂ key₂ K report B fuel₁ fuel₂ s₁ s₂ a).outer.state.reports ≤
        (TieBuffer.groupView key₁ K view₁ s₁).length *
          (TieBuffer.groupView key₂ K view₂ s₂).length ∧
    (run read₁ key₁ read₂ key₂ K report B fuel₁ fuel₂ s₁ s₂ a).outer.state.queries ≤
        (TieBuffer.groupView key₁ K view₁ s₁).length *
          ((TieBuffer.groupView key₂ K view₂ s₂).length + 1) ∧
    (run read₁ key₁ read₂ key₂ K report B fuel₁ fuel₂ s₁ s₂ a).outer.state.restores ≤
        (TieBuffer.groupView key₁ K view₁ s₁).length := by
  let filled := TieBuffer.fill read₂ key₂ K B s₂
  let long := TieBuffer.hasKey read₂ key₂ K filled.cursor
  let N := (TieBuffer.groupView key₂ K view₂ s₂).length
  let P := fun (st : State σ₂ τ) (r : ℕ) =>
    st.reports ≤ r * N ∧ st.queries ≤ r * (N + 1) ∧ st.restores ≤ r
  have hsplit : filled.buffer.size +
      (TieBuffer.groupView key₂ K view₂ filled.cursor).length = N := by
    have hb := congrArg List.length (TieBuffer.fill_buffer read₂ key₂ K view₂ hread₂ B s₂)
    rw [TieBuffer.fill_suffix read₂ key₂ K view₂ hread₂ B s₂]
    simp only [Array.length_toList, List.length_take] at hb
    simp only [List.length_drop]
    dsimp only [filled, N]
    omega
  have hstep : ∀ x st r, P st r →
      P (step read₂ key₂ K report filled.buffer filled.cursor long fuel₂ x st).1 (r + 1) := by
    intro x st r hr
    have h := step_bounds read₂ key₂ K report view₂ hread₂ filled.buffer filled.cursor long fuel₂ x st
    rw [hsplit] at h
    dsimp only [P] at hr ⊢
    rcases hr with ⟨hr, hq, hc⟩
    rcases h with ⟨hr', hq', hc'⟩
    rw [Nat.add_mul, Nat.add_mul]
    simp only [one_mul]
    exact ⟨hr'.trans (Nat.add_le_add_right hr _), hq'.trans (Nat.add_le_add_right hq _), by omega⟩
  have h := TieReplay.run_preserves read₁ key₁ K
    (step read₂ key₂ K report filled.buffer filled.cursor long fuel₂) P hstep fuel₁ s₁
    ⟨filled.cursor, a, 0, 0, 0⟩ (by simp [P])
  have hr := TieReplay.run_reports_le_potential read₁ key₁ K
    (step read₂ key₂ K report filled.buffer filled.cursor long fuel₂)
    view₁ hread₁ fuel₁ s₁ ⟨filled.cursor, a, 0, 0, 0⟩
  dsimp only [P] at h
  refine ⟨h.1.trans (Nat.mul_le_mul_right N hr),
    h.2.1.trans (Nat.mul_le_mul_right (N + 1) hr), h.2.2.trans hr⟩

/-- On a continuing run every occurrence in the Cartesian tie group is
reported, in first-stream order and then second-stream order. -/
theorem state_complete (read₁ : σ₁ → Option (α × σ₁)) (key₁ : α → ℤ)
    (read₂ : σ₂ → Option (β × σ₂)) (key₂ : β → ℤ) (K : ℤ)
    (report : α → β → τ → τ × Bool) (hreport : ∀ x y a, (report x y a).2 = false)
    (view₁ : σ₁ → List α) (hread₁ : RowMerge.IsReader read₁ view₁)
    (view₂ : σ₂ → List β) (hread₂ : RowMerge.IsReader read₂ view₂)
    (B fuel₁ fuel₂ : ℕ) (s₁ : σ₁) (s₂ : σ₂) (a : τ)
    (hfuel₁ : (TieBuffer.groupView key₁ K view₁ s₁).length ≤ fuel₁)
    (hfuel₂ : (TieBuffer.groupView key₂ K view₂ s₂).length ≤ fuel₂) :
    (run read₁ key₁ read₂ key₂ K report B fuel₁ fuel₂ s₁ s₂ a).outer.state.user =
      (TieBuffer.groupView key₁ K view₁ s₁).foldl
        (fun a x => (TieBuffer.groupView key₂ K view₂ s₂).foldl
          (fun a y => (report x y a).1) a) a := by
  let filled := TieBuffer.fill read₂ key₂ K B s₂
  let long := TieBuffer.hasKey read₂ key₂ K filled.cursor
  let f := step read₂ key₂ K report filled.buffer filled.cursor long fuel₂
  have hnonhalt : ∀ x st, (f x st).2 = false := by
    intro x st
    exact JoinOne.halted_false read₂ key₂ K (report x) (hreport x)
      filled.buffer filled.cursor long fuel₂ st.user
  have huser : ∀ x st, (f x st).1.user =
      (TieBuffer.groupView key₂ K view₂ s₂).foldl (fun a y => (report x y a).1) st.user := by
    intro x st
    exact JoinOne.filled_state_complete read₂ key₂ K (report x) (hreport x)
      view₂ hread₂ B fuel₂ s₂ st.user hfuel₂
  have h := TieReplay.run_state_complete read₁ key₁ K f hnonhalt view₁ hread₁ fuel₁ s₁
    (⟨filled.cursor, a, 0, 0, 0⟩ : State σ₂ τ) hfuel₁
  change (TieReplay.run read₁ key₁ K f fuel₁ s₁ _).state.user = _
  rw [h]
  exact (List.foldl_hom State.user (g₁ := fun st x => (f x st).1)
    (fun st x => (huser x st).symm)).symm

theorem step_halted_false (read₂ : σ₂ → Option (β × σ₂)) (key₂ : β → ℤ) (K : ℤ)
    (report : α → β → τ → τ × Bool) (hreport : ∀ x y a, (report x y a).2 = false)
    (buffer : Array β) (saved : σ₂) (long : Bool) (fuel₂ : ℕ) (x : α) (a : State σ₂ τ) :
    (step read₂ key₂ K report buffer saved long fuel₂ x a).2 = false :=
  JoinOne.halted_false read₂ key₂ K (report x) (hreport x) buffer saved long fuel₂ a.user

theorem halted_false (read₁ : σ₁ → Option (α × σ₁)) (key₁ : α → ℤ)
    (read₂ : σ₂ → Option (β × σ₂)) (key₂ : β → ℤ) (K : ℤ)
    (report : α → β → τ → τ × Bool) (hreport : ∀ x y a, (report x y a).2 = false)
    (B fuel₁ fuel₂ : ℕ) (s₁ : σ₁) (s₂ : σ₂) (a : τ) :
    (run read₁ key₁ read₂ key₂ K report B fuel₁ fuel₂ s₁ s₂ a).outer.halted = false :=
  TieReplay.run_halted_false read₁ key₁ K _
    (step_halted_false read₂ key₂ K report hreport _ _ _ _) _ _ _

/-- Both generator cursors end immediately after this key, so a surrounding
merge join can continue without losing its next different-key occurrences. -/
theorem views_complete (read₁ : σ₁ → Option (α × σ₁)) (key₁ : α → ℤ)
    (read₂ : σ₂ → Option (β × σ₂)) (key₂ : β → ℤ) (K : ℤ)
    (report : α → β → τ → τ × Bool) (hreport : ∀ x y a, (report x y a).2 = false)
    (view₁ : σ₁ → List α) (hread₁ : RowMerge.IsReader read₁ view₁)
    (view₂ : σ₂ → List β) (hread₂ : RowMerge.IsReader read₂ view₂)
    (B fuel₁ fuel₂ : ℕ) (s₁ : σ₁) (s₂ : σ₂) (a : τ)
    (hfuel₁ : (TieBuffer.groupView key₁ K view₁ s₁).length ≤ fuel₁)
    (hfuel₂ : (TieBuffer.groupView key₂ K view₂ s₂).length ≤ fuel₂)
    (hne : TieBuffer.groupView key₁ K view₁ s₁ ≠ []) :
    view₁ s₁ = TieBuffer.groupView key₁ K view₁ s₁ ++
        view₁ (run read₁ key₁ read₂ key₂ K report B fuel₁ fuel₂ s₁ s₂ a).outer.cursor ∧
    view₂ s₂ = TieBuffer.groupView key₂ K view₂ s₂ ++
        view₂ (run read₁ key₁ read₂ key₂ K report B fuel₁ fuel₂ s₁ s₂ a).outer.state.last := by
  let filled := TieBuffer.fill read₂ key₂ K B s₂
  let long := TieBuffer.hasKey read₂ key₂ K filled.cursor
  let f := step read₂ key₂ K report filled.buffer filled.cursor long fuel₂
  have hnonhalt : ∀ x st, (f x st).2 = false :=
    step_halted_false read₂ key₂ K report hreport filled.buffer filled.cursor long fuel₂
  have hspec := TieReplay.runAcc_nonhalting_spec read₁ key₁ K f hnonhalt view₁ hread₁ fuel₁ s₁
    (⟨filled.cursor, a, 0, 0, 0⟩ : State σ₂ τ) 0 0
  have hfirst : view₁ s₁ = TieBuffer.groupView key₁ K view₁ s₁ ++
      view₁ (run read₁ key₁ read₂ key₂ K report B fuel₁ fuel₂ s₁ s₂ a).outer.cursor := by
    simpa only [run, TieReplay.run, f, long, filled, List.take_of_length_le hfuel₁] using hspec.2.2.2
  refine ⟨hfirst, ?_⟩
  let P := fun (st : State σ₂ τ) (r : ℕ) => r = 0 ∨
    view₂ s₂ = TieBuffer.groupView key₂ K view₂ s₂ ++ view₂ st.last
  have hstep : ∀ x st r, P st r → P (f x st).1 (r + 1) := by
    intro x st r _
    exact Or.inr (JoinOne.filled_view_complete read₂ key₂ K (report x) (hreport x)
      view₂ hread₂ B fuel₂ s₂ st.user hfuel₂)
  have hP := TieReplay.run_preserves read₁ key₁ K f P hstep fuel₁ s₁
    (⟨filled.cursor, a, 0, 0, 0⟩ : State σ₂ τ) (Or.inl rfl)
  have hcount : (run read₁ key₁ read₂ key₂ K report B fuel₁ fuel₂ s₁ s₂ a).outer.reports =
      (TieBuffer.groupView key₁ K view₁ s₁).length := by
    simpa only [run, TieReplay.run, f, long, filled, Nat.zero_add, Nat.min_eq_right hfuel₁] using hspec.2.1
  change (run read₁ key₁ read₂ key₂ K report B fuel₁ fuel₂ s₁ s₂ a).outer.reports = 0 ∨ _ at hP
  rcases hP with hz | hP
  · rw [hcount] at hz
    exact False.elim (hne (List.length_eq_zero_iff.mp hz))
  · exact hP

theorem query_bound (read₁ : σ₁ → Option (α × σ₁)) (key₁ : α → ℤ)
    (read₂ : σ₂ → Option (β × σ₂)) (key₂ : β → ℤ) (K : ℤ)
    (report : α → β → τ → τ × Bool)
    (view₁ : σ₁ → List α) (hread₁ : RowMerge.IsReader read₁ view₁)
    (view₂ : σ₂ → List β) (hread₂ : RowMerge.IsReader read₂ view₂)
    (B fuel₁ fuel₂ : ℕ) (s₁ : σ₁) (s₂ : σ₂) (a : τ) :
    (run read₁ key₁ read₂ key₂ K report B fuel₁ fuel₂ s₁ s₂ a).outer.queries +
      (run read₁ key₁ read₂ key₂ K report B fuel₁ fuel₂ s₁ s₂ a).fillQueries +
      (run read₁ key₁ read₂ key₂ K report B fuel₁ fuel₂ s₁ s₂ a).outer.state.queries ≤
        2 * (TieBuffer.groupView key₁ K view₁ s₁).length +
        (TieBuffer.groupView key₂ K view₂ s₂).length +
        (TieBuffer.groupView key₁ K view₁ s₁).length *
          (TieBuffer.groupView key₂ K view₂ s₂).length + 2 := by
  have hq := (run_bounds read₁ key₁ read₂ key₂ K report view₁ hread₁ view₂ hread₂
    B fuel₁ fuel₂ s₁ s₂ a).2.1
  have hf := TieBuffer.fill_queries_le_potential read₂ key₂ K view₂ hread₂ B s₂
  have ho := TieReplay.run_queries_le_potential read₁ key₁ K
    (step read₂ key₂ K report (TieBuffer.fill read₂ key₂ K B s₂).buffer
      (TieBuffer.fill read₂ key₂ K B s₂).cursor
      (TieBuffer.hasKey read₂ key₂ K (TieBuffer.fill read₂ key₂ K B s₂).cursor) fuel₂)
    view₁ hread₁ fuel₁ s₁ ⟨(TieBuffer.fill read₂ key₂ K B s₂).cursor, a, 0, 0, 0⟩
  change (run read₁ key₁ read₂ key₂ K report B fuel₁ fuel₂ s₁ s₂ a).outer.queries ≤ _ at ho
  change (run read₁ key₁ read₂ key₂ K report B fuel₁ fuel₂ s₁ s₂ a).fillQueries ≤ _ at hf
  nlinarith

theorem bufferSize_le (read₁ : σ₁ → Option (α × σ₁)) (key₁ : α → ℤ)
    (read₂ : σ₂ → Option (β × σ₂)) (key₂ : β → ℤ) (K : ℤ)
    (report : α → β → τ → τ × Bool)
    (view₂ : σ₂ → List β) (hread₂ : RowMerge.IsReader read₂ view₂)
    (B fuel₁ fuel₂ : ℕ) (s₁ : σ₁) (s₂ : σ₂) (a : τ) :
    (run read₁ key₁ read₂ key₂ K report B fuel₁ fuel₂ s₁ s₂ a).bufferSize ≤ B :=
  TieBuffer.fill_size_le read₂ key₂ K view₂ hread₂ B s₂

/-- Without a long suffix, there are no generator restores. -/
theorem restores_eq_zero_of_short (read₁ : σ₁ → Option (α × σ₁)) (key₁ : α → ℤ)
    (read₂ : σ₂ → Option (β × σ₂)) (key₂ : β → ℤ) (K : ℤ)
    (report : α → β → τ → τ × Bool) (B fuel₁ fuel₂ : ℕ)
    (s₁ : σ₁) (s₂ : σ₂) (a : τ)
    (hshort : TieBuffer.hasKey read₂ key₂ K (TieBuffer.fill read₂ key₂ K B s₂).cursor = false) :
    (run read₁ key₁ read₂ key₂ K report B fuel₁ fuel₂ s₁ s₂ a).outer.state.restores = 0 := by
  dsimp only [run]
  apply TieReplay.run_preserves read₁ key₁ K _
    (fun (st : State σ₂ τ) (_ : ℕ) => st.restores = 0) _ _ _ _ rfl
  intro x st r hst
  simpa only [step, hshort, Bool.false_eq_true, ite_false, Nat.add_zero] using hst

/-- Every snapshot/restore is charged to potential partners, including
partners not reached when the execution halts. -/
theorem copies_charged (read₁ : σ₁ → Option (α × σ₁)) (key₁ : α → ℤ)
    (read₂ : σ₂ → Option (β × σ₂)) (key₂ : β → ℤ) (K : ℤ)
    (report : α → β → τ → τ × Bool)
    (view₁ : σ₁ → List α) (hread₁ : RowMerge.IsReader read₁ view₁)
    (view₂ : σ₂ → List β) (hread₂ : RowMerge.IsReader read₂ view₂)
    (B fuel₁ fuel₂ : ℕ) (s₁ : σ₁) (s₂ : σ₂) (a : τ) :
    B * ((if (run read₁ key₁ read₂ key₂ K report B fuel₁ fuel₂ s₁ s₂ a).snapshot then 1 else 0) +
      (run read₁ key₁ read₂ key₂ K report B fuel₁ fuel₂ s₁ s₂ a).outer.state.restores) ≤
      2 * ((TieBuffer.groupView key₁ K view₁ s₁).length *
        (TieBuffer.groupView key₂ K view₂ s₂).length) := by
  have hc := (run_bounds read₁ key₁ read₂ key₂ K report view₁ hread₁ view₂ hread₂
    B fuel₁ fuel₂ s₁ s₂ a).2.2
  by_cases hl : TieBuffer.hasKey read₂ key₂ K (TieBuffer.fill read₂ key₂ K B s₂).cursor = true
  · have hB := (TieBuffer.long_group_full_buffer read₂ key₂ K view₂ hread₂ B s₂ hl).1.le
    by_cases hfirst : TieBuffer.hasKey read₁ key₁ K s₁ = true
    · have hpos : 0 < (TieBuffer.groupView key₁ K view₁ s₁).length :=
        List.length_pos_iff.mpr ((TieBuffer.hasKey_iff read₁ key₁ K view₁ hread₁ s₁).mp hfirst)
      have hs : (run read₁ key₁ read₂ key₂ K report B fuel₁ fuel₂ s₁ s₂ a).snapshot = true := by
        simp [run, hl, hfirst]
      simp only [hs, ↓reduceIte]
      calc
        B * (1 + _) ≤ B * (2 * (TieBuffer.groupView key₁ K view₁ s₁).length) := by
          apply Nat.mul_le_mul_left
          omega
        _ ≤ (TieBuffer.groupView key₂ K view₂ s₂).length *
            (2 * (TieBuffer.groupView key₁ K view₁ s₁).length) := Nat.mul_le_mul_right _ hB
        _ = _ := by ring
    · have he : TieBuffer.groupView key₁ K view₁ s₁ = [] := by
        by_contra he
        exact hfirst ((TieBuffer.hasKey_iff read₁ key₁ K view₁ hread₁ s₁).mpr he)
      have hs : (run read₁ key₁ read₂ key₂ K report B fuel₁ fuel₂ s₁ s₂ a).snapshot = false := by
        simp [run, Bool.eq_false_iff.mpr hfirst]
      rw [he, List.length_nil] at hc ⊢
      simp [hs, Nat.eq_zero_of_le_zero hc]
  · have hshort := Bool.eq_false_iff.mpr hl
    have hz := restores_eq_zero_of_short read₁ key₁ read₂ key₂ K report B fuel₁ fuel₂ s₁ s₂ a hshort
    have hs : (run read₁ key₁ read₂ key₂ K report B fuel₁ fuel₂ s₁ s₂ a).snapshot = false := by
      simp [run, hshort]
    simp [hs, hz]

end TieGroup
end LowSpaceSubsetSum

end OAI
