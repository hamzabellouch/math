import Mathlib.Combinatorics.Matroid.Closure
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Order.Interval.Finset.Nat

namespace OAI

namespace MatroidProphet.MarkedPivots

open scoped BigOperators

abbrev Occurrences (r q : ℕ) := Fin r ⊕ Fin q

def label {α : Type*} {r q : ℕ} (old : Fin r → α) (movable : Fin q → α) :
    Occurrences r q → α := Sum.elim old movable

def mark {r q : ℕ} (oldMark : Fin r → Bool) (movableMark : Fin q → Bool) :
    Occurrences r q → Bool := Sum.elim oldMark movableMark

def OldOrdered {r q : ℕ} (time : Occurrences r q → ℕ) : Prop :=
  ∀ i j : Fin r, i < j → time (Sum.inl i) < time (Sum.inl j)

/-- The label is first spanned at this occurrence, and not before it. -/
def FirstSpans {α : Type*} {r q : ℕ} (M : Matroid α)
    (labels : Occurrences r q → α) (time : Occurrences r q → ℕ)
    (e : α) (o : Occurrences r q) : Prop :=
  e ∈ M.closure (labels '' {p | time p ≤ time o}) ∧
    e ∉ M.closure (labels '' {p | time p < time o})

/-- The finite set encodes precisely those test coordinates whose pivot has mark one. -/
def Records {α : Type*} {r q n : ℕ} (M : Matroid α)
    (old : Fin r → α) (movable : Fin q → α) (test : Fin n → α)
    (time : Occurrences r q → ℕ) (oldMark : Fin r → Bool)
    (movableMark : Fin q → Bool) (pattern : Finset (Fin n)) : Prop :=
  ∀ f, ∃ o, FirstSpans M (label old movable) time (test f) o ∧
    (mark oldMark movableMark o = true ↔ f ∈ pattern)

/-- All actual pivot-mark vectors over all interleavings and all movable marks. -/
noncomputable def patterns {α : Type*} {r q n : ℕ} (M : Matroid α)
    (old : Fin r → α) (movable : Fin q → α) (test : Fin n → α)
    (oldMark : Fin r → Bool) : Finset (Finset (Fin n)) := by
  classical
  exact Finset.univ.filter fun pattern =>
    ∃ time : Occurrences r q → ℕ, OldOrdered time ∧ Function.Injective time ∧
      ∃ movableMark : Fin q → Bool, Records M old movable test time oldMark movableMark pattern

/-- Full named source obligation, including well-definedness for every interleaving.
The test function is injective because the manuscript tests a set of `n` nonloops.
The conclusion actually remains true without that injectivity assumption. -/
def SourceContract.{u} : Prop :=
  ∀ {α : Type u} [Fintype α] (M : Matroid α) (r q n s : ℕ)
    (old : Fin r → α) (movable : Fin q → α) (test : Fin n → α)
    (oldMark : Fin r → Bool),
    q ≤ s → (∀ i, old i ∈ M.E) → (∀ i, movable i ∈ M.E) →
    M.closure (Set.range old) = M.E → Function.Injective test →
    (∀ f, test f ∈ M.E ∧ test f ∉ M.closure ∅) →
    (patterns M old movable test oldMark).card ≤
      4 ^ s * ∑ k ∈ Finset.Iic s, n.choose k ∧
    ∀ (time : Occurrences r q → ℕ), OldOrdered time → Function.Injective time →
      ∀ movableMark : Fin q → Bool,
        ∃! pattern, Records M old movable test time oldMark movableMark pattern

end MatroidProphet.MarkedPivots

end OAI
