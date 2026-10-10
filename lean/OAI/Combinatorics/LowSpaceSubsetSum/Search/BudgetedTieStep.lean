import OAI.Combinatorics.LowSpaceSubsetSum.Search.BudgetedOuterCompletion
import OAI.Combinatorics.LowSpaceSubsetSum.Streams.CountedTieGroup

namespace OAI

/-! # A prepaid callback for one outer tie occurrence -/

namespace LowSpaceSubsetSum.BudgetedTieStep

universe u v s t w
variable {α : Type u} {β : Type v} {σ : Type s} {τ : Type t}

def result (long : Bool) (st : TieGroup.State σ τ) (out : TieReplay.Result σ τ) :
    TieGroup.State σ τ × Bool :=
  (⟨out.cursor, out.state, st.queries + out.queries, st.reports + out.reports,
    st.restores + if long then 1 else 0⟩, out.halted)

def execute (charge copyCharge : ℕ) (read : σ → Option (β × σ) × ℕ)
    (key : β → ℤ × ℕ) (K : ℤ) (report : α → β → τ → (τ × Bool) × ℕ)
    (clone : σ → σ × ℕ) (buffer : Array β) (saved : σ) (long : Bool) (fuel : ℕ)
    (x : α) (st : TieGroup.State σ τ) (budget : ℕ) :
    Option ((TieGroup.State σ τ × Bool) × ℕ) × ℕ :=
  if 6 ≤ budget then
    let inner := BudgetedJoinOne.execute charge copyCharge read key K (report x) clone
      buffer saved long fuel st.user (budget - 6)
    (inner.1.map (fun (out, left) => (result long st out, left)), inner.2 + 6)
  else (none, 1)

def bill (charge copyCharge : ℕ) (read : σ → Option (β × σ) × ℕ)
    (key : β → ℤ × ℕ) (K : ℤ) (report : α → β → τ → (τ × Bool) × ℕ)
    (clone : σ → σ × ℕ) (buffer : Array β) (saved : σ) (long : Bool) (fuel : ℕ)
    (x : α) (st : TieGroup.State σ τ) : ℕ :=
  charge * ((CountedJoinOne.run read key K (report x) clone buffer saved long fuel st.user).1.queries + 2) +
    (if long then copyCharge else 0) + 12

theorem execute_value (charge copyCharge : ℕ) (read : σ → Option (β × σ) × ℕ)
    (key : β → ℤ × ℕ) (K : ℤ) (report : α → β → τ → (τ × Bool) × ℕ)
    (clone : σ → σ × ℕ) (buffer : Array β) (saved : σ) (long : Bool) (fuel : ℕ)
    (x : α) (st : TieGroup.State σ τ) (budget : ℕ) (out : TieGroup.State σ τ × Bool) (left : ℕ)
    (h : (execute charge copyCharge read key K report clone buffer saved long fuel x st budget).1 =
      some (out, left)) :
    out = (CountedTieGroup.step read key K report clone buffer saved long fuel x st).1 ∧
      left ≤ budget := by
  rw [execute] at h
  split at h
  next hb =>
    obtain ⟨pair, hi, he⟩ := Option.map_eq_some_iff.mp h
    rcases pair with ⟨inner, remaining⟩
    have hv := BudgetedJoinOne.execute_value charge copyCharge read key K (report x) clone
      buffer saved long fuel st.user (budget - 6) inner remaining hi
    cases he
    exact ⟨by rw [hv.1]; rfl, hv.2.trans (Nat.sub_le _ _)⟩
  next _ => contradiction

theorem execute_work (read : σ → Option (β × σ) × ℕ) (key : β → ℤ × ℕ) (K : ℤ)
    (report : α → β → τ → (τ × Bool) × ℕ) (clone : σ → σ × ℕ)
    (R L C charge copyCharge : ℕ) (hr : ∀ s, (read s).2 ≤ R)
    (hk : ∀ y, (key y).2 ≤ L) (hc : ∀ x y a, (report x y a).2 ≤ C)
    (hcharge : max R 4 + L + C + 8 ≤ charge) (hcopy : ∀ s, (clone s).2 ≤ copyCharge)
    (buffer : Array β) (saved : σ) (long : Bool) (fuel : ℕ)
    (x : α) (st : TieGroup.State σ τ) (budget : ℕ) :
    (execute charge copyCharge read key K report clone buffer saved long fuel x st budget).2 ≤
      budget + 1 := by
  have hi := BudgetedJoinOne.execute_work read key K (report x) clone R L C charge copyCharge
    hr hk (hc x) hcharge hcopy buffer saved long fuel st.user (budget - 6)
  rw [execute]
  split <;> dsimp only <;> omega

theorem execute_spent (read : σ → Option (β × σ) × ℕ) (key : β → ℤ × ℕ) (K : ℤ)
    (report : α → β → τ → (τ × Bool) × ℕ) (clone : σ → σ × ℕ)
    (R L C charge copyCharge : ℕ) (hr : ∀ s, (read s).2 ≤ R)
    (hk : ∀ y, (key y).2 ≤ L) (hc : ∀ x y a, (report x y a).2 ≤ C)
    (hcharge : max R 4 + L + C + 8 ≤ charge) (hcopy : ∀ s, (clone s).2 ≤ copyCharge)
    (buffer : Array β) (saved : σ) (long : Bool) (fuel : ℕ)
    (x : α) (st : TieGroup.State σ τ) (budget : ℕ) (out : TieGroup.State σ τ × Bool) (left : ℕ)
    (h : (execute charge copyCharge read key K report clone buffer saved long fuel x st budget).1 =
      some (out, left)) :
    left ≤ budget ∧
    (execute charge copyCharge read key K report clone buffer saved long fuel x st budget).2 ≤
      budget - left := by
  rw [execute] at h ⊢
  split at h
  next hb =>
    simp only [hb, ↓reduceIte]
    obtain ⟨pair, hi, he⟩ := Option.map_eq_some_iff.mp h
    rcases pair with ⟨inner, remaining⟩
    have hs := BudgetedJoinOne.execute_spent read key K (report x) clone R L C charge copyCharge
      hr hk (hc x) hcharge hcopy buffer saved long fuel st.user (budget - 6) inner remaining hi
    have hl := (BudgetedJoinOne.execute_value charge copyCharge read key K (report x) clone
      buffer saved long fuel st.user (budget - 6) inner remaining hi).2
    cases he
    try dsimp only
    omega
  next _ => contradiction

theorem execute_complete (charge copyCharge : ℕ) (read : σ → Option (β × σ) × ℕ)
    (key : β → ℤ × ℕ) (K : ℤ) (report : α → β → τ → (τ × Bool) × ℕ)
    (clone : σ → σ × ℕ) (buffer : Array β) (saved : σ) (long : Bool) (fuel : ℕ)
    (x : α) (st : TieGroup.State σ τ) (budget : ℕ)
    (hb : bill charge copyCharge read key K report clone buffer saved long fuel x st ≤ budget) :
    ∃ left, (execute charge copyCharge read key K report clone buffer saved long fuel x st budget).1 =
      some ((CountedTieGroup.step read key K report clone buffer saved long fuel x st).1, left) ∧
      budget ≤ left + bill charge copyCharge read key K report clone buffer saved long fuel x st := by
  have hguard : 6 ≤ budget := by unfold bill at hb; omega
  obtain ⟨left, hi⟩ := BudgetedJoinOne.execute_complete charge copyCharge read key K (report x) clone
    buffer saved long fuel st.user (budget - 6) (by unfold bill at hb; omega)
  have hr := BudgetedJoinOne.execute_remaining charge copyCharge read key K (report x) clone
    buffer saved long fuel st.user (budget - 6) _ left hi
  refine ⟨left, ?_, ?_⟩
  · rw [execute, ite_eq_left hguard]
    simp only [hi, Option.map_some]
    rfl
  · unfold bill
    omega

end LowSpaceSubsetSum.BudgetedTieStep

end OAI
