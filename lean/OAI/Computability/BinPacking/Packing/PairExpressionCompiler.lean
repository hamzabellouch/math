import Mathlib.Data.Fintype.Basic
import OAI.Computability.BinPacking.Arithmetic.NatExpressionBounds

namespace OAI

noncomputable section

namespace BinPackingGap.PairExpressionCompiler

open NatExpressionCompiler BinaryRegisterProgram

variable {α : Type} [DecidableEq α]

abbrev Reg (num den : Expr α) := α ⊕ (Node num ⊕ Node den)

def input (num den : Expr α) : α → Reg num den := Sum.inl

def numNodes (num den : Expr α) : Node num ↪ Reg num den where
  toFun n := .inr (.inl n)
  inj' := by intro a b h; exact Sum.inl.inj (Sum.inr.inj h)

def denNodes (num den : Expr α) : Node den ↪ Reg num den where
  toFun n := .inr (.inr n)
  inj' := by intro a b h; exact Sum.inr.inj (Sum.inr.inj h)

def initial (num den : Expr α) (values : α → Nat) : Reg num den → Nat
  | .inl a => values a
  | .inr _ => 0

def numCommands (num den : Expr α) : List (Command (Reg num den)) :=
  compileInto (input num den) num (numNodes num den) (by intros; simp [input, numNodes])

def denCommands (num den : Expr α) : List (Command (Reg num den)) :=
  compileInto (input num den) den (denNodes num den) (by intros; simp [input, denNodes])

def commands (num den : Expr α) := numCommands num den ++ denCommands num den

def numRoot (num den : Expr α) : Reg num den := numNodes num den (root num)
def denRoot (num den : Expr α) : Reg num den := denNodes num den (root den)

omit [DecidableEq α] in
theorem numRoot_ne_denRoot (num den : Expr α) : numRoot num den ≠ denRoot num den := by
  intro equal
  change (Sum.inr (Sum.inl (root num)) : Reg num den) = Sum.inr (Sum.inr (root den)) at equal
  cases Sum.inr.inj equal

theorem num_correct (num den : Expr α) :
    Correct (input num den) (numNodes num den) (root num)
      (fun v => eval v num) (numCommands num den) :=
  compileInto_correct _ _ _ _

theorem den_correct (num den : Expr α) :
    Correct (input num den) (denNodes num den) (root den)
      (fun v => eval v den) (denCommands num den) :=
  compileInto_correct _ _ _ _

theorem first_preserves_input (num den : Expr α) (values : α → Nat) (a : α) :
    resultOf (numCommands num den) (initial num den values) (input num den a) = values a := by
  have h := num_correct num den (initial num den values) (fun _ => rfl)
  exact h.2.2 _ (by intros; simp [input, numNodes])

theorem first_den_empty (num den : Expr α) (values : α → Nat) (n : Node den) :
    resultOf (numCommands num den) (initial num den values) (denNodes num den n) = 0 := by
  have h := num_correct num den (initial num den values) (fun _ => rfl)
  exact h.2.2 _ (by
    intro node equal
    change (Sum.inr (Sum.inr n) : Reg num den) = Sum.inr (Sum.inl node) at equal
    cases Sum.inr.inj equal)

theorem ready (num den : Expr α) (values : α → Nat) :
    Ready (commands num den) (initial num den values) := by
  rw [commands, Ready_append]
  exact ⟨(num_correct num den (initial num den values) (fun _ => rfl)).1,
    (den_correct num den _ (first_den_empty num den values)).1⟩

theorem numerator_output (num den : Expr α) (values : α → Nat) :
    resultOf (commands num den) (initial num den values) (numRoot num den) = eval values num := by
  rw [commands, resultOf_append]
  have hn := num_correct num den (initial num den values) (fun _ => rfl)
  have hd := den_correct num den _ (first_den_empty num den values)
  rw [hd.2.2 (numRoot num den) (by
    intro node equal
    change (Sum.inr (Sum.inl (root num)) : Reg num den) = Sum.inr (Sum.inr node) at equal
    cases Sum.inr.inj equal)]
  simpa only [numRoot, initial, input] using hn.2.1

theorem denominator_output (num den : Expr α) (values : α → Nat) :
    resultOf (commands num den) (initial num den values) (denRoot num den) = eval values den := by
  rw [commands, resultOf_append]
  have hd := den_correct num den _ (first_den_empty num den values)
  simpa only [denRoot, first_preserves_input] using hd.2.1

theorem preserves_input (num den : Expr α) (values : α → Nat) (a : α) :
    resultOf (commands num den) (initial num den values) (input num den a) = values a := by
  rw [commands, resultOf_append]
  have hd := den_correct num den _ (first_den_empty num den values)
  rw [hd.2.2 (input num den a) (by intros; simp [input, denNodes])]
  exact first_preserves_input num den values a

def clearList {Reg : Type} (registers : List Reg) : List (Command Reg) := registers.map Command.clear

theorem clearList_ready {Reg : Type} [DecidableEq Reg] (registers : List Reg) (values : Reg → Nat) :
    Ready (clearList registers) values := by
  induction registers generalizing values with
  | nil => trivial
  | cons r tail ih => exact ⟨True.intro, ih _⟩

theorem clearList_result {Reg : Type} [DecidableEq Reg]
    (registers : List Reg) (values : Reg → Nat) (r : Reg) :
    resultOf (clearList registers) values r = if r ∈ registers then 0 else values r := by
  induction registers generalizing values with
  | nil => simp [clearList]
  | cons s tail ih =>
    simp only [clearList, List.map_cons, resultOf_cons]
    rw [show tail.map Command.clear = clearList tail from rfl, ih]
    by_cases ht : r ∈ tail
    · simp [ht]
    · by_cases hs : r = s
      · subst r; simp [ht, result, destination, value]
      · simp [ht, hs, result, destination, value]

def temporaryList (num den : Expr α) : List (Reg num den) :=
  (Finset.univ : Finset (Node num ⊕ Node den)).toList.map Sum.inr

omit [DecidableEq α] in
theorem mem_temporaryList (num den : Expr α) (r : Reg num den) :
    r ∈ temporaryList num den ↔ ∃ n : Node num ⊕ Node den, r = Sum.inr n := by
  simp [temporaryList, eq_comm]

def clearCommands (num den : Expr α) := clearList (temporaryList num den)

theorem clear_ready (num den : Expr α) (values : Reg num den → Nat) :
    Ready (clearCommands num den) values := clearList_ready _ _

theorem clear_result (num den : Expr α) (values : Reg num den → Nat) :
    resultOf (clearCommands num den) values = initial num den (fun a => values (input num den a)) := by
  funext r
  rw [clearCommands, clearList_result]
  cases r with
  | inl a => simp [mem_temporaryList, initial, input]
  | inr n => simp [mem_temporaryList, initial]

def consumed (num den : Expr α) (values : Reg num den → Nat) : Reg num den → Nat :=
  Function.update (Function.update values (numRoot num den) 0) (denRoot num den) 0

theorem consumed_input (num den : Expr α) (values : Reg num den → Nat) (a : α) :
    consumed num den values (input num den a) = values (input num den a) := by
  simp [consumed, input, numRoot, denRoot, numNodes, denNodes]

theorem clear_after_consumed (num den : Expr α) (values : α → Nat) :
    resultOf (clearCommands num den)
      (consumed num den (resultOf (commands num den) (initial num den values))) =
        initial num den values := by
  rw [clear_result]
  congr 1
  funext a
  rw [consumed_input, preserves_input]

omit [DecidableEq α] in
theorem initial_width (num den : Expr α) (values : α → Nat) (width : Nat)
    (h : ∀ a, (values a).size ≤ width) :
    ∀ r, (initial num den values r).size ≤ width := by
  intro r
  cases r with
  | inl a => exact h a
  | inr n => simp [initial]

end BinPackingGap.PairExpressionCompiler

end

end OAI
