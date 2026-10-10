import OAI.Computability.PerfectCompleteness.Foundations.HierarchicalFrozenTablesLemmas
import OAI.Computability.PerfectCompleteness.Reduction.FixedCallBudgetLemmas

namespace OAI

section

namespace PerfectCompleteness.UpperScalarCutCalls

open DescendantSpaces
open scoped BigOperators Classical

noncomputable section

variable {branch : Nat → Nat} {n j i depth : Nat}

abbrev Index (rows repeats : Nat → Nat) (p : Path branch n j) (r : Path branch j i) :=
  OriginalCutCalls.Index rows repeats (p.append r) ⊕ TerminalCalls.TerminalIndex repeats r

def oldCall (rows repeats : Nat → Nat) (p : Path branch n j) (r : Path branch j i) :
    OriginalCutCalls.Index rows repeats (p.append r) → Index rows repeats p r := Sum.inl

def freshCall (rows repeats : Nat → Nat) (p : Path branch n j) (r : Path branch j i) :
    TerminalCalls.TerminalIndex repeats r → Index rows repeats p r := Sum.inr

theorem oldCall_injective (rows repeats : Nat → Nat)
    (p : Path branch n j) (r : Path branch j i) :
    Function.Injective (oldCall rows repeats p r) := by
  intro a b h
  exact Sum.inl.inj h

theorem freshCall_injective (rows repeats : Nat → Nat)
    (p : Path branch n j) (r : Path branch j i) :
    Function.Injective (freshCall rows repeats p r) := by
  intro a b h
  exact Sum.inr.inj h

theorem old_ne_fresh (rows repeats : Nat → Nat)
    (p : Path branch n j) (r : Path branch j i)
    (old : OriginalCutCalls.Index rows repeats (p.append r))
    (fresh : TerminalCalls.TerminalIndex repeats r) :
    oldCall rows repeats p r old ≠ freshCall rows repeats p r fresh := by
  intro h
  cases h

theorem old_fresh_disjoint (rows repeats : Nat → Nat)
    (p : Path branch n j) (r : Path branch j i) :
    Disjoint (Set.range (oldCall rows repeats p r))
      (Set.range (freshCall rows repeats p r)) := by
  refine Set.disjoint_left.mpr ?_
  rintro x ⟨old, rfl⟩ ⟨fresh, h⟩
  exact old_ne_fresh rows repeats p r old fresh h.symm

def count (rows repeats : Nat → Nat) (root upper lower : Nat) : Nat :=
  OriginalCutCalls.count rows repeats root lower +
    ∏ h ∈ Finset.Ioc lower upper, 2 * repeats h

theorem card_eq_count (rows repeats : Nat → Nat)
    (p : Path branch n j) (r : Path branch j i) :
    Fintype.card (Index rows repeats p r) = count rows repeats n j i := by
  simp only [Index, Fintype.card_sum, OriginalCutCalls.card_eq_count,
    TerminalCalls.card_eq_prod, count]

def numbering (rows repeats : Nat → Nat) (p : Path branch n j) (r : Path branch j i) :
    Index rows repeats p r ≃ Fin (count rows repeats n j i) :=
  Fintype.equivFinOfCardEq (card_eq_count rows repeats p r)

def terminalToOriginal (rows repeats : Nat → Nat) :
    {j i : Nat} → (r : Path branch j i) → BucketSampler.Direction (rows j) →
      TerminalCalls.TerminalIndex repeats r → OriginalCutCalls.Index rows repeats r
  | _, _, .refl _, a, _ => a
  | _, _, .step _ _, a, terminal => Sum.inl (a, terminal)

theorem terminalToOriginal_injective (rows repeats : Nat → Nat)
    (r : Path branch j i) (a : BucketSampler.Direction (rows j)) :
    Function.Injective (terminalToOriginal rows repeats r a) := by
  cases r with
  | refl j =>
      change Function.Injective (fun _ : Unit => a)
      intro x y _
      exact Subsingleton.elim x y
  | @step k l child q =>
      intro x y h
      exact congrArg Prod.snd (Sum.inl.inj h)

def terminalEmbedding (rows repeats : Nat → Nat)
    (r : Path branch j i) (a : BucketSampler.Direction (rows j)) :
    TerminalCalls.TerminalIndex repeats r ↪ OriginalCutCalls.Index rows repeats r :=
  ⟨terminalToOriginal rows repeats r a, terminalToOriginal_injective rows repeats r a⟩

theorem terminal_card_le_original (rows repeats : Nat → Nat)
    (r : Path branch j i) (a : BucketSampler.Direction (rows j)) :
    Fintype.card (TerminalCalls.TerminalIndex repeats r) ≤
      Fintype.card (OriginalCutCalls.Index rows repeats r) :=
  Fintype.card_le_of_injective (terminalToOriginal rows repeats r a)
    (terminalToOriginal_injective rows repeats r a)

theorem card_le_two_budget (rows repeats : Nat → Nat)
    (p : Path branch n j) (r : Path branch j i)
    (a : BucketSampler.Direction (rows j)) (hroot : n ≤ depth) :
    Fintype.card (Index rows repeats p r) ≤ 2 * FixedCallBudget.budget depth rows repeats := by
  have hold := FixedCallBudget.original_calls_le rows repeats (p.append r) hroot
  have hfresh := (terminal_card_le_original rows repeats r a).trans
    (FixedCallBudget.original_calls_le rows repeats r (p.height_le.trans hroot))
  change Fintype.card
    (OriginalCutCalls.Index rows repeats (p.append r) ⊕ TerminalCalls.TerminalIndex repeats r) ≤ _
  rw [Fintype.card_sum]
  omega

theorem count_le_two_budget (rows repeats : Nat → Nat)
    (p : Path branch n j) (r : Path branch j i)
    (a : BucketSampler.Direction (rows j)) (hroot : n ≤ depth) :
    count rows repeats n j i ≤ 2 * FixedCallBudget.budget depth rows repeats := by
  rw [← card_eq_count rows repeats p r]
  exact card_le_two_budget rows repeats p r a hroot

theorem card_le_budget_with_extra (rows repeats : Nat → Nat)
    (p : Path branch n j) (r : Path branch j i)
    (a : BucketSampler.Direction (rows j)) (hroot : n ≤ depth) :
    Fintype.card (Index rows repeats p r) ≤
      2 * FixedCallBudget.budget depth rows repeats + 1 :=
  (card_le_two_budget rows repeats p r a hroot).trans (Nat.le_succ _)

theorem count_le_budget_with_extra (rows repeats : Nat → Nat)
    (p : Path branch n j) (r : Path branch j i)
    (a : BucketSampler.Direction (rows j)) (hroot : n ≤ depth) :
    count rows repeats n j i ≤ 2 * FixedCallBudget.budget depth rows repeats + 1 :=
  (count_le_two_budget rows repeats p r a hroot).trans (Nat.le_succ _)

theorem card_le_fixed_calls {δ : ℚ} (plan : FixedRows.Plan δ)
    (p : Path branch n j) (r : Path branch j i)
    (a : BucketSampler.Direction (FixedRows.rows plan j)) (hroot : n ≤ plan.depth) :
    Fintype.card (Index (FixedRows.rows plan) (FixedRows.repeats plan) p r) ≤
      FixedParameters.calls plan := by
  simpa only [FixedParameters.calls] using
    card_le_budget_with_extra (FixedRows.rows plan) (FixedRows.repeats plan) p r a hroot

theorem count_le_fixed_calls {δ : ℚ} (plan : FixedRows.Plan δ)
    (p : Path branch n j) (r : Path branch j i)
    (a : BucketSampler.Direction (FixedRows.rows plan j)) (hroot : n ≤ plan.depth) :
    count (FixedRows.rows plan) (FixedRows.repeats plan) n j i ≤ FixedParameters.calls plan := by
  simpa only [FixedParameters.calls] using
    count_le_budget_with_extra (FixedRows.rows plan) (FixedRows.repeats plan) p r a hroot

end
end PerfectCompleteness.UpperScalarCutCalls

end

end OAI
