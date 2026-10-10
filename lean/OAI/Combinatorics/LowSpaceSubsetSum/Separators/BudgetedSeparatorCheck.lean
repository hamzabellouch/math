import OAI.Combinatorics.LowSpaceSubsetSum.Separators.BudgetedSeparatorTraversal
import OAI.Combinatorics.LowSpaceSubsetSum.Separators.BudgetedSeparatorTerminal
import OAI.Combinatorics.LowSpaceSubsetSum.Separators.StoredSeparatorCheck

namespace OAI

/-! # A fully budgeted checker on the four prepared blocks

Cached lengths drive every guard. The terminal sort, each pair of filters,
and the next block are reached only after their allowances are available.
The callback result carries the unspent allowance into the next branch.
-/

namespace LowSpaceSubsetSum.BudgetedSeparatorCheck

open BudgetedSeparatorCall BudgetedSeparatorFlow StoredSeparatorCheck

variable {n g : ℕ}

def header (capacity nx ny budget : ℕ) : Outcome Bool :=
  BudgetedSeparatorCall.run 4 (fun _ => (decide (nx + ny ≤ capacity), 3)) budget

private theorem header_account (capacity nx ny budget : ℕ) :
    Account budget (header capacity nx ny budget) :=
  ⟨BudgetedSeparatorCall.work _ _ _ (by norm_num),
    fun a left h => BudgetedSeparatorCall.spent _ _ _ (by norm_num) a left h⟩

def execute (capacity : ℕ) (target : ℤ) :
    List (Block n g) → List (StoredEntry n) → List (StoredEntry n) →
      ℕ → ℕ → ℕ → Outcome Bool
  | [], xs, ys, nx, ny, budget =>
    bind (header capacity nx ny budget) fun fits left =>
      if fits then BudgetedSeparatorTerminal.run target xs ys nx ny left
      else pure false left
  | b :: rest, xs, ys, nx, ny, budget =>
    bind (header capacity nx ny budget) fun fits left =>
      if fits then
        BudgetedSeparatorTraversal.execute b.queryBound b.leftQuery b.rightQuery
          (fun _ as bs na nb remaining => execute capacity target rest as bs na nb remaining)
          b.depth 0 b.familySize xs ys nx ny left
      else pure false left

theorem account (capacity : ℕ) (target : ℤ) (blocks : List (Block n g))
    (xs ys : List (StoredEntry n)) (nx ny budget : ℕ)
    (hx : xs.length = nx) (hy : ys.length = ny) :
    Account budget (execute capacity target blocks xs ys nx ny budget) := by
  induction blocks generalizing xs ys nx ny budget with
  | nil =>
    rw [execute]
    apply bind_account _ _ _ (header_account _ _ _ _)
    intro fits left _
    split
    · exact ⟨BudgetedSeparatorTerminal.work target xs ys nx ny left hx hy,
        fun result remaining h => BudgetedSeparatorTerminal.spent target xs ys nx ny left
          hx hy result remaining h⟩
    · exact pure_account _ _
  | cons b rest ih =>
    rw [execute]
    apply bind_account _ _ _ (header_account _ _ _ _)
    intro fits left _
    split
    · exact BudgetedSeparatorTraversal.account b.queryBound b.leftQuery b.rightQuery
        b.leftQuery_work b.rightQuery_work
        (fun _ as bs na nb remaining => execute capacity target rest as bs na nb remaining)
        (fun _ as bs na nb remaining ha hb => ih as bs na nb remaining ha hb)
        b.depth 0 b.familySize xs ys nx ny left hx hy
    · exact pure_account _ _

def reference (capacity : ℕ) (target : ℤ) :
    List (Block n g) → List (StoredEntry n) → List (StoredEntry n) → Bool × ℕ
  | [], xs, ys =>
    if xs.length + ys.length ≤ capacity then
      ((StoredEntryTerminal.run target xs ys).1,
        4 + BudgetedSeparatorTerminal.charge n xs.length ys.length)
    else (false, 4)
  | b :: rest, xs, ys =>
    if xs.length + ys.length ≤ capacity then
      let out := BudgetedSeparatorTraversal.reference b.queryBound b.leftQuery b.rightQuery
        (fun _ as bs => reference capacity target rest as bs) b.depth 0 b.familySize xs ys
      (out.1, 4 + out.2)
    else (false, 4)

end LowSpaceSubsetSum.BudgetedSeparatorCheck

end OAI
