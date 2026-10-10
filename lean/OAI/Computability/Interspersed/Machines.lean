import Mathlib

namespace OAI

/-! Finite transition tables and two-sided machine executions. -/

noncomputable section
open scoped ContDiff
namespace PrefixFlows
inductive Move where
  | stay | right | left
  deriving DecidableEq, Repr

def Move.displacement : Move → ℤ
  | .stay => 0
  | .right => 1
  | .left => -1

def Move.code : Move → ℕ
  | .stay => 0
  | .right => 1
  | .left => 2

structure Instruction where
  nextState : ℕ
  writeSymbol : ℕ
  motion : Move
  deriving DecidableEq, Repr

 

structure Machine where
  alphabetSize : ℕ
  blank : ℕ
  initialState : ℕ
  haltStates : List ℕ
  table : List (List (Option Instruction))
  deriving DecidableEq, Repr

namespace Machine

def WellFormed (M : Machine) : Prop :=
  0 < M.alphabetSize ∧ M.blank < M.alphabetSize ∧
  M.initialState < M.table.length ∧
  (∀ q ∈ M.haltStates, q < M.table.length) ∧
  (∀ row ∈ M.table, row.length = M.alphabetSize ∧
    ∀ instruction ∈ row, ∀ a, instruction = some a →
      a.nextState < M.table.length ∧ a.writeSymbol < M.alphabetSize)

def ValidInput (M : Machine) (w : List ℕ) : Prop :=
  ∀ a ∈ w, a < M.alphabetSize

 
def code (M : Machine) : ℕ :=
  Encodable.encode (M.alphabetSize, M.blank, M.initialState, M.haltStates,
    M.table.map (List.map (Option.map fun a =>
      (a.nextState, a.writeSymbol, a.motion.code))))

def instruction (M : Machine) (q a : ℕ) : Option Instruction :=
  (M.table[q]?).bind fun row => (row[a]?).join

structure Configuration where
  state : ℕ
  head : ℤ
  tape : ℤ → ℕ

 

def initial (M : Machine) (w : List ℕ) : Configuration where
  state := M.initialState
  head := 0
  tape := fun j => if 0 ≤ j then (w[j.toNat]?).getD M.blank else M.blank

def step (M : Machine) (c : Configuration) : Option Configuration :=
  if c.state ∈ M.haltStates then none else
    (M.instruction c.state (c.tape c.head)).map fun a =>
      { state := a.nextState
        head := c.head + a.motion.displacement
        tape := Function.update c.tape c.head a.writeSymbol }

def run (M : Machine) (w : List ℕ) : ℕ → Option Configuration
  | 0 => some (M.initial w)
  | n + 1 => (M.run w n).bind M.step

 
def Halts (M : Machine) (w : List ℕ) : Prop :=
  ∃ n c, M.run w n = some c ∧ M.step c = none

end Machine
end PrefixFlows
end

end OAI
