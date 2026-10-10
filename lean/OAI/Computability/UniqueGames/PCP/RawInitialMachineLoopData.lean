import Mathlib.Data.List.FinRange
import OAI.Computability.UniqueGames.PCP.RawInitialMachineStart
import OAI.Computability.UniqueGames.PCP.RawInitialTablesLemmas

namespace OAI

section

/-! The exact input and output streams at successive clause-loop iterations.
These tape invariants use the actual word codecs and clause occurrence order. -/

namespace UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData

open Target Complexity RawInitialMachineModel

def clauseInput {n : Nat} (clauses : List (Clause n)) : List Bool :=
  encodeWords (clauses.flatMap Complexity.clauseWords)

@[simp] theorem clauseInput_nil (n : Nat) : clauseInput ([] : List (Clause n)) = [] := rfl

@[simp] theorem clauseInput_cons {n : Nat} (c : Clause n) (cs : List (Clause n)) :
    clauseInput (c :: cs) = encodeWords (Complexity.clauseWords c) ++ clauseInput cs := by
  simp only [clauseInput, List.flatMap_cons, encodeWords_append]

def clauseOutput (n i : Nat) (clauses : List (Clause n)) : List Nat :=
  (clauses.mapIdx fun offset c => RawInitialRows.clauseWords n (i + offset)
    (RawInitialRows.clauseNames c) (RawInitialRows.clauseSigns c)).flatten

private theorem mapIdx_ofFn {α β : Type} (xs : List α) (f : Nat → α → β) :
    xs.mapIdx f = List.ofFn (fun i : Fin xs.length => f i.val (xs.get i)) := by
  induction xs generalizing f with
  | nil => simp
  | cons x xs ih => simp [ih]

@[simp] theorem clauseOutput_nil (n i : Nat) : clauseOutput n i [] = [] := rfl

@[simp] theorem clauseOutput_cons (n i : Nat) (c : Clause n) (cs : List (Clause n)) :
    clauseOutput n i (c :: cs) =
      RawInitialRows.clauseWords n i (RawInitialRows.clauseNames c)
        (RawInitialRows.clauseSigns c) ++ clauseOutput n (i + 1) cs := by
  simp only [clauseOutput, List.mapIdx_cons, Nat.add_zero, List.flatten_cons,
    Nat.add_comm, Nat.add_left_comm]

theorem clauseOutput_numbered (F : Formula) :
    clauseOutput F.variables 0 F.clauses =
      (List.finRange F.clauses.length).flatMap (fun i =>
        RawInitialRows.clauseWords F.variables i.val
          (RawInitialRows.clauseNames (clauseAt F i))
          (RawInitialRows.clauseSigns (clauseAt F i))) := by
  simp only [clauseOutput, mapIdx_ofFn, List.ofFn_eq_map,
    Nat.zero_add, clauseAt]
  rfl

theorem tableWords_decomposition (F : Formula) :
    GraphTables.tableWords (RawInitialTables.table F) =
      [F.variables + F.clauses.length + 1, 6 * F.clauses.length + 1] ++
        clauseOutput F.variables 0 F.clauses ++
          RawInitialRows.dummyWords F.variables F.clauses.length := by
  rw [RawInitialRows.tableWords_eq, clauseOutput_numbered]

def loopTapes (n i remaining : Nat) (input reversed : List Bool) : Tape → List Bool
  | .input => input
  | .variables => encodeWord n
  | .counter => encodeWord remaining
  | .index => encodeWord i
  | .reversed => reversed
  | _ => []

theorem startTapes_eq (n m : Nat) (input : List Bool) :
    RawInitialMachineStart.startTapes n m input =
      loopTapes n 0 m input (encodeWords [n + m + 1, 6 * m + 1]).reverse := by
  funext tape
  cases tape <;> rfl

theorem decrement_counter (n i remaining : Nat) (input reversed : List Bool) :
    Function.update (loopTapes n i (remaining + 1) input reversed)
      Tape.counter (encodeWord remaining) = loopTapes n i remaining input reversed := by
  funext tape
  cases tape <;> simp [loopTapes]

theorem increment_index (n i remaining : Nat) (input reversed : List Bool) :
    Function.update (loopTapes n i remaining input reversed)
      Tape.index (true :: encodeWord i) = loopTapes n (i + 1) remaining input reversed := by
  funext tape
  cases tape <;> simp [loopTapes, encodeWord, List.replicate_succ]

end UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData

end

end OAI
