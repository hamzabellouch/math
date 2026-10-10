import OAI.Combinatorics.LowSpaceSubsetSum.Streams.MergeCorrectness

namespace OAI

/-!
# Sortedness of complete and stopped row merges

Only each row's individual order is required. The tournament minimum is
no larger than every remaining occurrence; replacing its front by its
successor preserves this invariant. Every finite trace is therefore sorted,
including traces stopped by the operation cap.
-/

namespace LowSpaceSubsetSum
namespace RowMerge

universe u v

variable {α : Type u} {σ : Type v} {d : ℕ}

def RowsSorted (key : α → ℤ) (view : σ → List α)
    (t : Tournament.Tree (Front d α σ) d) : Prop :=
  ∀ p, (remaining view t p).Pairwise (fun x y => key x ≤ key y)

theorem replacement_remaining_subset (key : α → ℤ) (read : σ → Option (α × σ))
    (view : σ → List α) (hread : IsReader read view)
    (t : Tournament.Tree (Front d α σ) d)
    (ht : Tournament.Valid (fun y => key y.value) t) (halign : Aligned t)
    {x : Front d α σ} (hx : Tournament.winner t = some x) (p : Path d) :
    remaining view (Tournament.replace (fun y => key y.value) t x.row
      (front read x.row x.after)) p ⊆ remaining view t p := by
  have hnew := replace_remaining key read view hread t x p
  have hrow := winner_at_own_row key t ht halign hx
  rw [hnew]
  by_cases hp : x.row = p
  · subst p
    rw [ite_eq_left rfl]
    simp only [remaining, hrow]
    intro y hy
    exact List.mem_cons_of_mem _ hy
  · rw [ite_eq_right hp]

theorem replacement_rowsSorted (key : α → ℤ) (read : σ → Option (α × σ))
    (view : σ → List α) (hread : IsReader read view)
    (t : Tournament.Tree (Front d α σ) d)
    (ht : Tournament.Valid (fun y => key y.value) t) (halign : Aligned t)
    (hsort : RowsSorted key view t) {x : Front d α σ}
    (hx : Tournament.winner t = some x) :
    RowsSorted key view (Tournament.replace (fun y => key y.value) t x.row
      (front read x.row x.after)) := by
  intro p
  rw [replace_remaining key read view hread t x p]
  by_cases hp : x.row = p
  · subst p
    rw [ite_eq_left rfl]
    have hs := hsort x.row
    have hrow := winner_at_own_row key t ht halign hx
    simp only [remaining, hrow] at hs
    exact (List.pairwise_cons.mp hs).2
  · rw [ite_eq_right hp]
    exact hsort p

theorem winner_le_remaining (key : α → ℤ) (view : σ → List α)
    (t : Tournament.Tree (Front d α σ) d)
    (ht : Tournament.Valid (fun y => key y.value) t) (hsort : RowsSorted key view t)
    {x : Front d α σ} (hx : Tournament.winner t = some x)
    (p : Path d) {y : α} (hy : y ∈ remaining view t p) : key x.value ≤ key y := by
  cases hp : Tournament.lookup t p with
  | none => simp [remaining, hp] at hy
  | some z =>
    have hmin := winner_is_minimum key t ht hx p hp
    have hs := hsort p
    simp only [remaining, hp] at hy hs
    rcases List.mem_cons.mp hy with hy | hy
    · simpa [hy] using hmin
    · exact hmin.trans ((List.pairwise_cons.mp hs).1 y hy)

theorem trace_lower_bound (key : α → ℤ) (read : σ → Option (α × σ))
    (view : σ → List α) (hread : IsReader read view) (k : ℕ)
    (t : Tournament.Tree (Front d α σ) d)
    (ht : Tournament.Valid (fun y => key y.value) t) (halign : Aligned t)
    (c : ℤ) (hc : ∀ p, ∀ y ∈ remaining view t p, c ≤ key y) :
    ∀ y ∈ trace key read k t, c ≤ key y := by
  induction k generalizing t with
  | zero => simp [trace]
  | succ k ih =>
    cases hw : Tournament.winner t with
    | none => simp [trace, advance, hw]
    | some x =>
      let t' := Tournament.replace (fun y => key y.value) t x.row (front read x.row x.after)
      have ha : advance key read t = some (x.value, t') := by simp [advance, hw, t']
      have ht' := advance_valid key read t ht ha
      have halign' := advance_aligned key read t halign ha
      have hrow := winner_at_own_row key t ht halign hw
      have hfront : c ≤ key x.value := hc x.row x.value (by simp [remaining, hrow])
      have hc' : ∀ p, ∀ y ∈ remaining view t' p, c ≤ key y := by
        intro p y hy
        exact hc p y (replacement_remaining_subset key read view hread t ht halign hw p hy)
      rw [trace, ha]
      intro y hy
      rcases List.mem_cons.mp hy with hy | hy
      · simpa [hy] using hfront
      · exact ih t' ht' halign' hc' y hy

theorem trace_sorted (key : α → ℤ) (read : σ → Option (α × σ))
    (view : σ → List α) (hread : IsReader read view) (k : ℕ)
    (t : Tournament.Tree (Front d α σ) d)
    (ht : Tournament.Valid (fun y => key y.value) t) (halign : Aligned t)
    (hsort : RowsSorted key view t) :
    (trace key read k t).Pairwise (fun x y => key x ≤ key y) := by
  induction k generalizing t with
  | zero => simp [trace]
  | succ k ih =>
    cases hw : Tournament.winner t with
    | none => simp [trace, advance, hw]
    | some x =>
      let t' := Tournament.replace (fun y => key y.value) t x.row (front read x.row x.after)
      have ha : advance key read t = some (x.value, t') := by simp [advance, hw, t']
      have ht' := advance_valid key read t ht ha
      have halign' := advance_aligned key read t halign ha
      have hsort' := replacement_rowsSorted key read view hread t ht halign hsort hw
      rw [trace, ha]
      apply List.pairwise_cons.mpr
      refine ⟨?_, ih t' ht' halign' hsort'⟩
      apply trace_lower_bound key read view hread k t' ht' halign' (key x.value)
      intro p y hy
      exact winner_le_remaining key view t ht hsort hw p
        (replacement_remaining_subset key read view hread t ht halign hw p hy)

end RowMerge
end LowSpaceSubsetSum

end OAI
