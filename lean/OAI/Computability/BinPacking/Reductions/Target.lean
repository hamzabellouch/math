import Std

namespace OAI

namespace BinPackingGames.Foundations.Target

structure Literal (variables : Nat) where
  variableIndex : Fin variables
  positive : Bool
  deriving DecidableEq

def Literal.eval {n : Nat} (literal : Literal n) (assignment : Fin n → Bool) : Bool :=
  if literal.positive then assignment literal.variableIndex else !(assignment literal.variableIndex)

abbrev Clause (variables : Nat) := Vector (Literal variables) 3

def Clause.eval {n : Nat} (clause : Clause n) (assignment : Fin n → Bool) : Bool :=
  (clause[0].eval assignment || clause[1].eval assignment) || clause[2].eval assignment

structure Formula where
  variables : Nat
  clauses : List (Clause variables)

def Formula.Satisfiable (formula : Formula) : Prop :=
  ∃ assignment : Fin formula.variables → Bool,
    ∀ clause ∈ formula.clauses, clause.eval assignment = true

structure PermutationTable (alphabet : Nat) where
  images : Vector (Fin alphabet) alphabet
  inverseImages : Vector (Fin alphabet) alphabet
  leftInverse : ∀ label : Fin alphabet, inverseImages[images[label]] = label
  rightInverse : ∀ label : Fin alphabet, images[inverseImages[label]] = label

theorem PermutationTable.images_injective {q : Nat} (table : PermutationTable q)
    {x y : Fin q} (h : table.images[x] = table.images[y]) : x = y := by
  have inverseEquality := congrArg (fun label : Fin q => table.inverseImages[label]) h
  simpa only [table.leftInverse] using inverseEquality

theorem PermutationTable.images_surjective {q : Nat} (table : PermutationTable q)
    (label : Fin q) : ∃ preimage : Fin q, table.images[preimage] = label :=
  ⟨table.inverseImages[label], table.rightInverse label⟩

structure Constraint (vertices alphabet : Nat) where
  source : Fin vertices
  target : Fin vertices
  permutation : PermutationTable alphabet

def Constraint.satisfied {n q : Nat} (constraint : Constraint n q)
    (labeling : Fin n → Fin q) : Bool :=
  decide (constraint.permutation.images[labeling constraint.source] = labeling constraint.target)

structure Instance (alphabet : Nat) where
  vertices : Nat
  constraints : List (Constraint vertices alphabet)
  nonempty : constraints ≠ []

def countSatisfied {n q : Nat} (labeling : Fin n → Fin q) :
    List (Constraint n q) → Nat
  | [] => 0
  | constraint :: rest =>
      (if constraint.satisfied labeling then 1 else 0) + countSatisfied labeling rest

theorem countSatisfied_le_length {n q : Nat} (labeling : Fin n → Fin q)
    (constraints : List (Constraint n q)) :
    countSatisfied labeling constraints ≤ constraints.length := by
  induction constraints with
  | nil => simp [countSatisfied]
  | cons constraint rest ih =>
      simp only [countSatisfied, List.length_cons]
      split <;> omega

theorem Instance.constraintCount_positive {q : Nat} (game : Instance q) :
    0 < game.constraints.length := by
  cases h : game.constraints with
  | nil => exact False.elim (game.nonempty h)
  | cons constraint rest => simp

structure RationalError where
  numerator : Nat
  denominator : Nat
  numeratorPositive : 0 < numerator
  denominatorPositive : 0 < denominator
  belowHalf : 2 * numerator < denominator

def CompleteAt {q : Nat} (error : RationalError) (game : Instance q) : Prop :=
  ∃ labeling : Fin game.vertices → Fin q,
    error.denominator * game.constraints.length ≤
      error.denominator * countSatisfied labeling game.constraints +
      error.numerator * game.constraints.length

def SoundAt {q : Nat} (error : RationalError) (game : Instance q) : Prop :=
  ∀ labeling : Fin game.vertices → Fin q,
    error.denominator * countSatisfied labeling game.constraints ≤
      error.numerator * game.constraints.length

structure SemanticGapReduction (completenessError soundnessError : RationalError) where
  alphabet : Nat
  alphabetAtLeastTwo : 2 ≤ alphabet
  reduce : Formula → Instance alphabet
  completeness : ∀ formula : Formula,
    formula.Satisfiable → CompleteAt completenessError (reduce formula)
  soundness : ∀ formula : Formula,
    ¬ formula.Satisfiable → SoundAt soundnessError (reduce formula)

end BinPackingGames.Foundations.Target

end OAI
