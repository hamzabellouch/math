import Mathlib

namespace OAI

namespace UniqueGames.BinaryFormula

structure Literal where
  name : Nat
  positive : Bool
  deriving DecidableEq

def Literal.eval (literal : Literal) (assignment : Nat → Bool) : Bool :=
  if literal.positive then assignment literal.name else !(assignment literal.name)

abbrev Clause := Vector Literal 3

def Clause.eval (clause : Clause) (assignment : Nat → Bool) : Bool :=
  (clause[0].eval assignment || clause[1].eval assignment) || clause[2].eval assignment

structure Formula where
  clauses : List Clause

def Formula.Satisfiable (F : Formula) : Prop :=
  ∃ assignment : Nat → Bool, ∀ clause ∈ F.clauses, clause.eval assignment = true

def clauseNames (clause : Clause) : List Nat :=
  [clause[0].name, clause[1].name, clause[2].name]

def sourceNames (F : Formula) : List Nat :=
  F.clauses.flatMap clauseNames

end UniqueGames.BinaryFormula

end OAI
