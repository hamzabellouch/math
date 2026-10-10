import Mathlib
import OAI.Computability.DirectedFeedback.Machines.MachineEmbedding

namespace OAI


namespace DFVSGames.Foundations.Target

structure Literal («variables» : Nat) where
  variableIndex : Fin «variables»
  positive : Bool
  deriving DecidableEq

def Literal.eval {n : Nat} (literal : Literal n) (assignment : Fin n → Bool) : Bool :=
  if literal.positive then assignment literal.variableIndex else !(assignment literal.variableIndex)

abbrev Clause («variables» : Nat) := Vector (Literal «variables») 3

def Clause.eval {n : Nat} (clause : Clause n) (assignment : Fin n → Bool) : Bool :=
  (clause[0].eval assignment || clause[1].eval assignment) || clause[2].eval assignment

structure Formula where
  «variables» : Nat
  clauses : List (Clause «variables»)

def Formula.Satisfiable (formula : Formula) : Prop :=
  ∃ assignment : Fin formula.«variables» → Bool,
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

end DFVSGames.Foundations.Target


namespace DFVSGames.Foundations.Complexity

def encodeWord (n : Nat) : List Bool := List.replicate n true ++ [false]

def encodeWords : List Nat → List Bool
  | [] => []
  | n :: ns => encodeWord n ++ encodeWords ns

def decodeWordsAux : List Bool → Nat → Option (List Nat)
  | [], 0 => some []
  | [], _ + 1 => none
  | true :: bs, n => decodeWordsAux bs (n + 1)
  | false :: bs, n => (decodeWordsAux bs 0).map (n :: ·)

def decodeWords (bs : List Bool) : Option (List Nat) := decodeWordsAux bs 0

theorem decodeWordsAux_word (n k : Nat) (bs : List Bool) :
    decodeWordsAux (encodeWord n ++ bs) k =
      (decodeWordsAux bs 0).map ((k + n) :: ·) := by
  induction n generalizing k with
  | zero => simp [encodeWord, decodeWordsAux]
  | succ n ih =>
      simp only [encodeWord, List.replicate_succ, List.cons_append, List.append_assoc,
        decodeWordsAux]
      simpa [encodeWord, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (k + 1)

@[simp] theorem decodeWords_encodeWords (ns : List Nat) :
    decodeWords (encodeWords ns) = some ns := by
  induction ns with
  | nil => rfl
  | cons n ns ih =>
      simp only [decodeWords, encodeWords, decodeWordsAux_word, Nat.zero_add]
      simpa [decodeWords] using congrArg (Option.map (n :: ·)) ih

theorem encodeWords_injective {xs ys : List Nat} (h : encodeWords xs = encodeWords ys) :
    xs = ys := by
  have decoded := congrArg decodeWords h
  simpa only [decodeWords_encodeWords, Option.some.injEq] using decoded

@[simp] theorem encodeWord_length (n : Nat) : (encodeWord n).length = n + 1 := by
  simp [encodeWord]

@[simp] theorem encodeWords_append (xs ys : List Nat) :
    encodeWords (xs ++ ys) = encodeWords xs ++ encodeWords ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [encodeWords, ih, List.append_assoc]

@[simp] theorem encodeWords_length (ns : List Nat) :
    (encodeWords ns).length = ns.sum + ns.length := by
  induction ns with
  | nil => rfl
  | cons n ns ih => simp [encodeWords, ih]; omega

theorem encodeWords_length_le (ns : List Nat) (bound : Nat)
    (bounded : ∀ n ∈ ns, n ≤ bound) :
    (encodeWords ns).length ≤ ns.length * (bound + 1) := by
  induction ns with
  | nil => simp [encodeWords]
  | cons n ns ih =>
      have hn := bounded n (by simp)
      have hns := ih (fun x hx => bounded x (by simp [hx]))
      simp only [encodeWords, List.length_append, encodeWord_length, List.length_cons,
        Nat.add_mul, Nat.one_mul]
      omega

open Target

def literalWords {n : Nat} (literal : Literal n) : List Nat :=
  [literal.variableIndex.val, if literal.positive then 1 else 0]

def clauseWords {n : Nat} (clause : Clause n) : List Nat :=
  literalWords clause[0] ++ literalWords clause[1] ++ literalWords clause[2]

def formulaWords (formula : Formula) : List Nat :=
  [formula.«variables», formula.clauses.length] ++ formula.clauses.flatMap clauseWords

def formulaBits (formula : Formula) : List Bool := encodeWords (formulaWords formula)

@[simp] theorem literalWords_length {n : Nat} (literal : Literal n) :
    (literalWords literal).length = 2 := by simp [literalWords]

@[simp] theorem clauseWords_length {n : Nat} (clause : Clause n) :
    (clauseWords clause).length = 6 := by simp [clauseWords]

theorem clausesWords_length {n : Nat} (clauses : List (Clause n)) :
    (clauses.flatMap clauseWords).length = 6 * clauses.length := by
  induction clauses with
  | nil => rfl
  | cons clause clauses ih =>
      simp only [List.flatMap_cons, List.length_append, clauseWords_length,
        List.length_cons, ih, Nat.mul_add, Nat.mul_one]
      omega

@[simp] theorem formulaWords_length (formula : Formula) :
    (formulaWords formula).length = 2 + 6 * formula.clauses.length := by
  simp only [formulaWords, List.length_append, List.length_cons, List.length_nil,
    clausesWords_length]

theorem literalBits_length_le {n : Nat} (literal : Literal n) :
    (encodeWords (literalWords literal)).length ≤ n + 2 := by
  have hindex := literal.variableIndex.isLt
  cases hp : literal.positive <;> simp [literalWords, hp]

theorem clauseBits_length_le {n : Nat} (clause : Clause n) :
    (encodeWords (clauseWords clause)).length ≤ 3 * (n + 2) := by
  have h0 := literalBits_length_le clause[0]
  have h1 := literalBits_length_le clause[1]
  have h2 := literalBits_length_le clause[2]
  simp only [clauseWords, encodeWords_append, List.length_append]
  omega

theorem clausesBits_length_le {n : Nat} (clauses : List (Clause n)) :
    (encodeWords (clauses.flatMap clauseWords)).length ≤ clauses.length * (3 * (n + 2)) := by
  induction clauses with
  | nil => simp [encodeWords]
  | cons clause clauses ih =>
      have hc := clauseBits_length_le clause
      simp only [List.flatMap_cons, encodeWords_append, List.length_append,
        List.length_cons, Nat.add_mul, Nat.one_mul]
      omega

theorem formulaBits_length_le (formula : Formula) :
    (formulaBits formula).length ≤
      formula.«variables» + formula.clauses.length + 2 +
        formula.clauses.length * (3 * (formula.«variables» + 2)) := by
  have h := clausesBits_length_le formula.clauses
  simp only [formulaBits, formulaWords, encodeWords_append, List.length_append,
    encodeWords, encodeWord_length, List.length_nil]
  omega

end DFVSGames.Foundations.Complexity


namespace DFVSGames.Foundations.Hastad.SourceMachine

open Turing
open DFVSGames.Foundations.Complexity

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

def fieldLoop (source destination : K) (loopLabel : Λ) (exit : Option Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  .pop source (fun state head => (state.1, head))
    (.branch (fun state => state.2.getD false)
      (.push destination (fun _ => true) (.goto fun _ => loopLabel))
      (.load (fun state => (state.1, none))
        (Reduction.MachineTransfer.exitAt destination exit)))

def fieldStart (destination : K) (loopLabel : Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  .push destination (fun _ => false) (.goto fun _ => loopLabel)

def fieldTapes (source destination : K) (base : K → List Bool)
    (input output : List Bool) : K → List Bool :=
  Function.update (Function.update base source input) destination output

@[simp] theorem fieldTapes_source (source destination : K) (hne : source ≠ destination)
    (base : K → List Bool) (input output : List Bool) :
    fieldTapes source destination base input output source = input := by
  simp [fieldTapes, hne]

@[simp] theorem fieldTapes_destination (source destination : K)
    (base : K → List Bool) (input output : List Bool) :
    fieldTapes source destination base input output destination = output := by
  simp [fieldTapes]

@[simp] theorem fieldTapes_self (source destination : K) (base : K → List Bool) :
    fieldTapes source destination base (base source) (base destination) = base := by
  simp [fieldTapes]

theorem fieldTapes_other (source destination p : K)
    (hpS : p ≠ source) (hpD : p ≠ destination)
    (base : K → List Bool) (input output : List Bool) :
    fieldTapes source destination base input output p = base p := by
  simp [fieldTapes, hpS, hpD]

private theorem update_field_source_inline_SourceMachine (source destination : K) (hne : source ≠ destination)
    (base : K → List Bool) (input output replacement : List Bool) :
    Function.update (fieldTapes source destination base input output) source replacement =
      fieldTapes source destination base replacement output := by
  funext p
  by_cases hs : p = source
  · subst p; simp [fieldTapes, hne]
  · by_cases hd : p = destination
    · subst p; simp [fieldTapes, Ne.symm hne]
    · simp [fieldTapes, hs, hd]

private theorem update_field_destination_inline_SourceMachine (source destination : K)
    (base : K → List Bool) (input output replacement : List Bool) :
    Function.update (fieldTapes source destination base input output) destination replacement =
      fieldTapes source destination base input replacement := by
  simp [fieldTapes]

theorem fieldStep_delimiter (source destination : K) (hne : source ≠ destination)
    (loopLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atLoop : program loopLabel = fieldLoop source destination loopLabel exit)
    (base : K → List Bool) (suffix output : List Bool) (ambient : σ) (register : Option Bool) :
    TM2.step program
      ⟨some loopLabel, (ambient, register), fieldTapes source destination base (false :: suffix) output⟩ =
      some ⟨exit, (ambient, none), fieldTapes source destination base suffix output⟩ := by
  change some (TM2.stepAux (program loopLabel) (ambient, register)
    (fieldTapes source destination base (false :: suffix) output)) = _
  rw [atLoop]
  cases exit <;>
    simp [fieldLoop, Reduction.MachineTransfer.exitAt, TM2.stepAux, hne, update_field_source_inline_SourceMachine]

theorem fieldStep_true (source destination : K) (hne : source ≠ destination)
    (loopLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atLoop : program loopLabel = fieldLoop source destination loopLabel exit)
    (base : K → List Bool) (input output : List Bool) (ambient : σ) (register : Option Bool) :
    TM2.step program
      ⟨some loopLabel, (ambient, register), fieldTapes source destination base (true :: input) output⟩ =
      some ⟨some loopLabel, (ambient, some true),
        fieldTapes source destination base input (true :: output)⟩ := by
  change some (TM2.stepAux (program loopLabel) (ambient, register)
    (fieldTapes source destination base (true :: input) output)) = _
  rw [atLoop]
  simp [fieldLoop, TM2.stepAux, hne, update_field_source_inline_SourceMachine, update_field_destination_inline_SourceMachine]

theorem fieldLoopTrace (source destination : K) (hne : source ≠ destination)
    (loopLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atLoop : program loopLabel = fieldLoop source destination loopLabel exit)
    (base : K → List Bool) (n : Nat) (suffix output : List Bool)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[n + 1]
      (some ⟨some loopLabel, (ambient, register),
        fieldTapes source destination base (encodeWord n ++ suffix) output⟩) =
      some ⟨exit, (ambient, none),
        fieldTapes source destination base suffix (List.replicate n true ++ output)⟩ := by
  induction n generalizing output register with
  | zero =>
    simpa only [Nat.zero_add, Function.iterate_one, MachineComposition.advance_some,
      encodeWord, List.replicate_zero, List.nil_append, List.singleton_append] using
      fieldStep_delimiter source destination hne loopLabel exit program atLoop
        base suffix output ambient register
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    simp only [encodeWord, List.replicate_succ, List.cons_append]
    change (MachineComposition.advance (TM2.step program))^[n + 1]
      (TM2.step program ⟨some loopLabel, (ambient, register),
        fieldTapes source destination base (true :: (encodeWord n ++ suffix)) output⟩) = _
    rw [fieldStep_true source destination hne loopLabel exit program atLoop, ih]
    have hrotate : List.replicate n true ++ true :: output =
        true :: (List.replicate n true ++ output) := by
      calc
        _ = (List.replicate n true ++ [true]) ++ output := by simp
        _ = List.replicate (n + 1) true ++ output := by rw [List.replicate_succ']
        _ = _ := by rw [List.replicate_succ, List.cons_append]
    rw [hrotate]

theorem fieldStartStep (source destination : K)
    (startLabel loopLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atStart : program startLabel = fieldStart destination loopLabel)
    (base : K → List Bool) (input output : List Bool) (ambient : σ) (register : Option Bool) :
    TM2.step program
      ⟨some startLabel, (ambient, register), fieldTapes source destination base input output⟩ =
      some ⟨some loopLabel, (ambient, register),
        fieldTapes source destination base input (false :: output)⟩ := by
  change some (TM2.stepAux (program startLabel) (ambient, register)
    (fieldTapes source destination base input output)) = _
  rw [atStart]
  simp [fieldStart, TM2.stepAux, update_field_destination_inline_SourceMachine]

def fieldInTime (source destination : K) (hne : source ≠ destination)
    (startLabel loopLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atStart : program startLabel = fieldStart destination loopLabel)
    (atLoop : program loopLabel = fieldLoop source destination loopLabel exit)
    (base : K → List Bool) (n : Nat) (suffix : List Bool)
    (hinput : base source = encodeWord n ++ suffix)
    (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some startLabel, (ambient, register), base⟩
      (some ⟨exit, (ambient, none),
        fieldTapes source destination base suffix (encodeWord n ++ base destination)⟩)
      (n + 2) where
  steps := n + 2
  evals_in_steps := by
    have hbase : fieldTapes source destination base (encodeWord n ++ suffix)
        (base destination) = base := by rw [← hinput, fieldTapes_self]
    conv_lhs => rw [← hbase]
    change (MachineComposition.advance (TM2.step program))^[(n + 1) + 1]
      (some ⟨some startLabel, (ambient, register),
        fieldTapes source destination base (encodeWord n ++ suffix) (base destination)⟩) = _
    rw [Function.iterate_succ_apply]
    change (MachineComposition.advance (TM2.step program))^[n + 1]
      (TM2.step program ⟨some startLabel, (ambient, register),
        fieldTapes source destination base (encodeWord n ++ suffix) (base destination)⟩) = _
    rw [fieldStartStep source destination startLabel loopLabel program atStart,
      fieldLoopTrace source destination hne loopLabel exit program atLoop]
    simp [encodeWord, List.append_assoc]
  steps_le_m := Nat.le_refl _

def afterField (source destination : K) (base : K → List Bool)
    (n : Nat) (suffix : List Bool) : K → List Bool :=
  fieldTapes source destination base suffix (encodeWord n ++ base destination)

def fieldNext (start : Fin 4 → Λ) (exit : Option Λ) (j : Fin 4) : Option Λ :=
  match j.val with
  | 0 => some (start 1)
  | 1 => some (start 2)
  | 2 => some (start 3)
  | _ => exit

def fourTapes (source : K) (destination : Fin 4 → K) (base : K → List Bool)
    (a b c d : Nat) (suffix : List Bool) : K → List Bool :=
  let t₀ := afterField source (destination 0) base a (encodeWords [b, c, d] ++ suffix)
  let t₁ := afterField source (destination 1) t₀ b (encodeWords [c, d] ++ suffix)
  let t₂ := afterField source (destination 2) t₁ c (encodeWords [d] ++ suffix)
  afterField source (destination 3) t₂ d suffix

theorem fourTapes_source (source : K) (destination : Fin 4 → K)
    (hsep : ∀ j, source ≠ destination j) (base : K → List Bool)
    (a b c d : Nat) (suffix : List Bool) :
    fourTapes source destination base a b c d suffix source = suffix := by
  simp [fourTapes, afterField, hsep]

theorem fourTapes_other (source : K) (destination : Fin 4 → K)
    (p : K) (hpS : p ≠ source) (hpD : ∀ j, p ≠ destination j)
    (base : K → List Bool) (a b c d : Nat) (suffix : List Bool) :
    fourTapes source destination base a b c d suffix p = base p := by
  simp [fourTapes, afterField, fieldTapes_other, hpS, hpD]

theorem fourField_time_eq_length (a b c d : Nat) :
    a + b + c + d + 8 = (encodeWords [a, b, c, d]).length + 4 := by
  simp [encodeWords, encodeWord]
  omega

def fourFieldsInTime (source : K) (destination : Fin 4 → K)
    (hsep : ∀ j, source ≠ destination j)
    (start loopLabel : Fin 4 → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atStart : ∀ j, program (start j) = fieldStart (destination j) (loopLabel j))
    (atLoop : ∀ j, program (loopLabel j) =
      fieldLoop source (destination j) (loopLabel j) (fieldNext start exit j))
    (base : K → List Bool) (a b c d : Nat) (suffix : List Bool)
    (hinput : base source = encodeWords [a, b, c, d] ++ suffix)
    (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (start 0), (ambient, register), base⟩
      (some ⟨exit, (ambient, none), fourTapes source destination base a b c d suffix⟩)
      (a + b + c + d + 8) := by
  let t₀ := afterField source (destination 0) base a (encodeWords [b, c, d] ++ suffix)
  let t₁ := afterField source (destination 1) t₀ b (encodeWords [c, d] ++ suffix)
  let t₂ := afterField source (destination 2) t₁ c (encodeWords [d] ++ suffix)
  have h₀ : base source = encodeWord a ++ (encodeWords [b, c, d] ++ suffix) := by
    simpa only [encodeWords, List.append_assoc] using hinput
  have h₁ : t₀ source = encodeWord b ++ (encodeWords [c, d] ++ suffix) := by
    simp [t₀, afterField, hsep, encodeWords, List.append_assoc]
  have h₂ : t₁ source = encodeWord c ++ (encodeWords [d] ++ suffix) := by
    simp [t₁, afterField, hsep, encodeWords, List.append_assoc]
  have h₃ : t₂ source = encodeWord d ++ suffix := by
    simp [t₂, afterField, hsep, encodeWords]
  have p₀ := fieldInTime source (destination 0) (hsep 0) (start 0) (loopLabel 0)
    (some (start 1)) program (atStart 0) (atLoop 0) base a
    (encodeWords [b, c, d] ++ suffix) h₀ ambient register
  have p₁ := fieldInTime source (destination 1) (hsep 1) (start 1) (loopLabel 1)
    (some (start 2)) program (atStart 1) (atLoop 1) t₀ b
    (encodeWords [c, d] ++ suffix) h₁ ambient none
  have p₂ := fieldInTime source (destination 2) (hsep 2) (start 2) (loopLabel 2)
    (some (start 3)) program (atStart 2) (atLoop 2) t₁ c
    (encodeWords [d] ++ suffix) h₂ ambient none
  have p₃ := fieldInTime source (destination 3) (hsep 3) (start 3) (loopLabel 3)
    exit program (atStart 3) (atLoop 3) t₂ d suffix h₃ ambient none
  let p₀₁ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ p₀ p₁
  let p₀₁₂ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ p₀₁ p₂
  let p := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ p₀₁₂ p₃
  exact {
    toEvalsTo := p.toEvalsTo
    steps_le_m := by have h := p.steps_le_m; omega
  }

def fieldDestination (j : Fin 4) : Fin 5 := ⟨j.val + 1, by omega⟩

theorem fourTapes_concrete (base : Fin 5 → List Bool) (a b c d : Nat) (suffix : List Bool) :
    fourTapes 0 fieldDestination base a b c d suffix =
      fun p : Fin 5 => if p = 0 then suffix
        else if p = 1 then encodeWord a ++ base 1
        else if p = 2 then encodeWord b ++ base 2
        else if p = 3 then encodeWord c ++ base 3
        else encodeWord d ++ base 4 := by
  funext p
  have hp : p = 0 ∨ p = 1 ∨ p = 2 ∨ p = 3 ∨ p = 4 := by omega
  rcases hp with rfl | rfl | rfl | rfl | rfl <;>
    simp [fourTapes, afterField, fieldTapes, fieldDestination]

def groupingProgram (label : Fin 4 × Bool) :
    TM2.Stmt (fun _ : Fin 5 => Bool) (Fin 4 × Bool) (Unit × Option Bool) :=
  if label.2 then
    fieldLoop 0 (fieldDestination label.1) (label.1, true)
      (fieldNext (fun j => (j, false)) none label.1)
  else fieldStart (fieldDestination label.1) (label.1, true)

def groupingMachine : FinTM2 where
  K := Fin 5
  k₀ := 0
  k₁ := 1
  Γ _ := Bool
  Λ := Fin 4 × Bool
  main := (0, false)
  σ := Unit × Option Bool
  initialState := ((), none)
  m := groupingProgram

def groupingMachineInTime (base : Fin 5 → List Bool) (a b c d : Nat) (suffix : List Bool)
    (hinput : base 0 = encodeWords [a, b, c, d] ++ suffix) (register : Option Bool) :
    StateTransition.EvalsToInTime groupingMachine.step
      ⟨some (0, false), ((), register), base⟩
      (some ⟨none, ((), none), fourTapes (0 : Fin 5) fieldDestination base a b c d suffix⟩)
      (a + b + c + d + 8) :=
  fourFieldsInTime (0 : Fin 5) fieldDestination (by
    intro j h
    have hh := congrArg Fin.val h
    change 0 = j.val + 1 at hh
    omega)
    (fun j => (j, false)) (fun j => (j, true)) none groupingProgram
    (by intro j; simp [groupingProgram]) (by intro j; simp [groupingProgram])
    base a b c d suffix hinput () register

end DFVSGames.Foundations.Hastad.SourceMachine


namespace DFVSGames.Foundations.Complexity.MachineDrain

open Turing

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

def drain (source : K) (again : Λ) (exit : Option Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  .pop source (fun state head => (state.1, head))
    (.branch (fun state => state.2.isSome)
      (.goto fun _ => again)
      (.load (fun state => (state.1, none)) (Reduction.MachineTransfer.exitAt source exit)))

theorem drainTrace (source : K) (again : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atDrain : program again = drain source again exit)
    (base : K → List Bool) (word : List Bool) (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[word.length + 1]
      (some ⟨some again, (ambient, register), Function.update base source word⟩) =
      some ⟨exit, (ambient, none), Function.update base source []⟩ := by
  induction word generalizing register with
  | nil =>
      change some (TM2.stepAux (program again) (ambient, register)
        (Function.update base source [])) = _
      rw [atDrain]
      cases exit <;> simp [drain, TM2.stepAux, Reduction.MachineTransfer.exitAt]
  | cons symbol word ih =>
      rw [List.length_cons, Function.iterate_succ_apply]
      change (MachineComposition.advance (TM2.step program))^[word.length + 1]
        (some (TM2.stepAux (program again) (ambient, register)
          (Function.update base source (symbol :: word)))) = _
      rw [atDrain]
      simpa [drain, TM2.stepAux] using ih (some symbol)

def drainInTime (source : K) (again : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atDrain : program again = drain source again exit)
    (base : K → List Bool) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some again, (ambient, register), base⟩
      (some ⟨exit, (ambient, none), Function.update base source []⟩)
      ((base source).length + 1) where
  steps := (base source).length + 1
  evals_in_steps := by
    change (MachineComposition.advance (TM2.step program))^[(base source).length + 1]
      (some ⟨some again, (ambient, register), base⟩) = _
    simpa only [Function.update_eq_self] using
      drainTrace source again exit program atDrain base (base source) ambient register
  steps_le_m := Nat.le_refl _

end DFVSGames.Foundations.Complexity.MachineDrain


namespace DFVSGames.Foundations.Complexity.MachineFiniteSequence

open Turing MachineComposition

variable {Command : Type} (LocalLabel : Command → Type)

def Label : List Command → Type
  | [] => Empty
  | command :: commands => LocalLabel command ⊕ Label commands

instance labelFintype [∀ command, Fintype (LocalLabel command)]
    (commands : List Command) : Fintype (Label LocalLabel commands) := by
  induction commands with
  | nil => exact inferInstanceAs (Fintype Empty)
  | cons command commands ih =>
      letI := ih
      exact inferInstanceAs (Fintype (LocalLabel command ⊕ Label LocalLabel commands))

instance labelDecidableEq [∀ command, DecidableEq (LocalLabel command)]
    (commands : List Command) : DecidableEq (Label LocalLabel commands) := by
  induction commands with
  | nil => exact inferInstanceAs (DecidableEq Empty)
  | cons command commands ih =>
      letI := ih
      exact inferInstanceAs (DecidableEq (LocalLabel command ⊕ Label LocalLabel commands))

variable (main : ∀ command, LocalLabel command)
variable {K Λ σ : Type} {Γ : K → Type}

def entry : (commands : List Command) → (Label LocalLabel commands → Λ) → Option Λ → Option Λ
  | [], _, exit => exit
  | command :: _, labels, _ => some (labels (.inl (main command)))

variable (localInstruction : ∀ command, (LocalLabel command → Λ) → Option Λ →
  LocalLabel command → TM2.Stmt Γ Λ σ)

def instruction : (commands : List Command) → (Label LocalLabel commands → Λ) → Option Λ →
    Label LocalLabel commands → TM2.Stmt Γ Λ σ
  | [], _, _, label => nomatch label
  | command :: commands, labels, exit, .inl label =>
      localInstruction command (fun l => labels (.inl l))
        (entry LocalLabel main commands (fun l => labels (.inr l)) exit) label
  | _ :: commands, labels, exit, .inr label =>
      instruction commands (fun l => labels (.inr l)) exit label

variable {Data : Type} (result : Command → Data → Data) (cost : Command → Data → Nat)

def resultOf : List Command → Data → Data
  | [], data => data
  | command :: commands, data => resultOf commands (result command data)

def steps : List Command → Data → Nat
  | [], _ => 0
  | command :: commands, data => cost command data + steps commands (result command data)

variable [DecidableEq K]

theorem trace (program : Λ → TM2.Stmt Γ Λ σ)
    (invariant : Data → Prop) (state : Data → σ) (tapes : Data → ∀ k, List (Γ k))
    (commands : List Command)
    (localInvariant : ∀ command ∈ commands, ∀ data, invariant data →
      invariant (result command data))
    (localTrace : ∀ command ∈ commands, ∀ (labels : LocalLabel command → Λ) (exit : Option Λ),
      (∀ l, program (labels l) = localInstruction command labels exit l) →
      ∀ data, invariant data →
      (advance (TM2.step program))^[cost command data]
        (some ⟨some (labels (main command)), state data, tapes data⟩) =
      some ⟨exit, state (result command data), tapes (result command data)⟩)
    (labels : Label LocalLabel commands → Λ) (exit : Option Λ)
    (atLabels : ∀ l, program (labels l) =
      instruction LocalLabel main localInstruction commands labels exit l)
    (data : Data) (valid : invariant data) :
    (advance (TM2.step program))^[steps result cost commands data]
      (some ⟨entry LocalLabel main commands labels exit, state data, tapes data⟩) =
    some ⟨exit, state (resultOf result commands data), tapes (resultOf result commands data)⟩ := by
  induction commands generalizing data with
  | nil => rfl
  | cons command commands ih =>
      have firstRun := localTrace command (by simp)
        (fun l => labels (.inl l))
        (entry LocalLabel main commands (fun l => labels (.inr l)) exit)
        (fun l => atLabels (.inl l)) data valid
      have nextValid := localInvariant command (by simp) data valid
      have tailRun := ih
        (fun c hc d hd => localInvariant c (by simp [hc]) d hd)
        (fun c hc => localTrace c (by simp [hc]))
        (fun l => labels (.inr l)) (fun l => atLabels (.inr l))
        (result command data) nextValid
      rw [steps, Nat.add_comm, Function.iterate_add_apply]
      change (advance (TM2.step program))^[steps result cost commands (result command data)]
        ((advance (TM2.step program))^[cost command data]
          (some ⟨some (labels (.inl (main command))), state data, tapes data⟩)) = _
      rw [firstRun]
      exact tailRun

end DFVSGames.Foundations.Complexity.MachineFiniteSequence


namespace DFVSGames.Foundations.Complexity.MachineDrainMany

open Turing MachineComposition

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool
abbrev Tapes (K : Type) := K → List Bool
abbrev LocalLabel (_ : K) := Unit
abbrev Label (chosen : List K) := MachineFiniteSequence.Label (LocalLabel (K := K)) chosen
abbrev Data (K : Type) := Tapes K × Option Bool

def entry (chosen : List K) (labels : Label chosen → Λ) (exit : Option Λ) : Option Λ :=
  MachineFiniteSequence.entry (LocalLabel (K := K)) (fun _ => ()) chosen labels exit

def localInstruction (source : K) (labels : Unit → Λ) (exit : Option Λ) (_ : Unit) :
    TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  MachineDrain.drain source (labels ()) exit

def instruction (chosen : List K) (labels : Label chosen → Λ) (exit : Option Λ) :
    Label chosen → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  MachineFiniteSequence.instruction (LocalLabel (K := K)) (fun _ => ())
    localInstruction chosen labels exit

def result (source : K) (data : Data K) : Data K :=
  (Function.update data.1 source [], none)

def cost (source : K) (data : Data K) : Nat := (data.1 source).length + 1

def finalTapes : List K → Tapes K → Tapes K
  | [], base => base
  | source :: chosen, base => finalTapes chosen (Function.update base source [])

def finalRegister : List K → Option Bool → Option Bool
  | [], register => register
  | _ :: _, _ => none

omit [DecidableEq K] in
@[simp] theorem finalRegister_none (chosen : List K) : finalRegister chosen none = none := by
  cases chosen <;> rfl

def steps : List K → Tapes K → Nat
  | [], _ => 0
  | source :: chosen, base => (base source).length + 1 +
      steps chosen (Function.update base source [])

@[simp] theorem sequence_result (chosen : List K) (base : Tapes K) (register : Option Bool) :
    MachineFiniteSequence.resultOf result chosen (base, register) =
      (finalTapes chosen base, finalRegister chosen register) := by
  induction chosen generalizing base register with
  | nil => rfl
  | cons source chosen ih =>
      change MachineFiniteSequence.resultOf result chosen (Function.update base source [], none) =
        (finalTapes chosen (Function.update base source []), none)
      rw [ih, finalRegister_none]

@[simp] theorem sequence_steps (chosen : List K) (base : Tapes K) (register : Option Bool) :
    MachineFiniteSequence.steps result cost chosen (base, register) = steps chosen base := by
  induction chosen generalizing base register with
  | nil => rfl
  | cons source chosen ih =>
      simp only [MachineFiniteSequence.steps, result, cost, steps, ih]

theorem finalTapes_apply (chosen : List K) (base : Tapes K) (k : K) :
    finalTapes chosen base k = if k ∈ chosen then [] else base k := by
  induction chosen generalizing base with
  | nil => simp [finalTapes]
  | cons source chosen ih =>
      rw [finalTapes, ih]
      by_cases h : k = source
      · subst k
        simp
      · simp [List.mem_cons, h]

theorem finalTapes_mem (chosen : List K) (base : Tapes K) (k : K) (h : k ∈ chosen) :
    finalTapes chosen base k = [] := by rw [finalTapes_apply, ite_eq_left h]

theorem finalTapes_not_mem (chosen : List K) (base : Tapes K) (k : K) (h : k ∉ chosen) :
    finalTapes chosen base k = base k := by rw [finalTapes_apply, ite_eq_right h]

def lengthSum (chosen : List K) (base : Tapes K) : Nat :=
  (chosen.map (fun k => (base k).length)).sum

omit [DecidableEq K] in
theorem lengthSum_mono (chosen : List K) (first second : Tapes K)
    (h : ∀ k, (first k).length ≤ (second k).length) :
    lengthSum chosen first ≤ lengthSum chosen second := by
  induction chosen with
  | nil => exact Nat.le_refl 0
  | cons source chosen ih =>
      simp only [lengthSum, List.map_cons, List.sum_cons] at ih ⊢
      exact Nat.add_le_add (h source) ih

theorem steps_le (chosen : List K) (base : Tapes K) :
    steps chosen base ≤ lengthSum chosen base + chosen.length := by
  induction chosen generalizing base with
  | nil => simp [steps, lengthSum]
  | cons source chosen ih =>
      have hshort : ∀ k, ((Function.update base source []) k).length ≤ (base k).length := by
        intro k
        by_cases h : k = source
        · subst k
          simp
        · simp [Function.update_of_ne h]
      have hsum := lengthSum_mono chosen (Function.update base source []) base hshort
      have htail := ih (Function.update base source [])
      simp only [steps, lengthSum, List.map_cons, List.sum_cons, List.length_cons] at hsum htail ⊢
      omega

theorem steps_le_uniform (chosen : List K) (base : Tapes K) (bound : Nat)
    (h : ∀ k, (base k).length ≤ bound) :
    steps chosen base ≤ chosen.length * (bound + 1) := by
  have hsum : lengthSum chosen base ≤ chosen.length * bound := by
    induction chosen with
    | nil => simp [lengthSum]
    | cons source chosen ih =>
        simp only [lengthSum, List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul,
          Nat.one_mul] at ih ⊢
        have hs := h source
        omega
  have hc := steps_le chosen base
  rw [Nat.mul_add, Nat.mul_one]
  omega

theorem trace (chosen : List K) (labels : Label chosen → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atLabels : ∀ l, program (labels l) = instruction chosen labels exit l)
    (base : Tapes K) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[steps chosen base]
      (some ⟨entry chosen labels exit, (ambient, register), base⟩) =
    some ⟨exit, (ambient, finalRegister chosen register), finalTapes chosen base⟩ := by
  have run := MachineFiniteSequence.trace
    (LocalLabel := LocalLabel (K := K)) (main := fun _ => ())
    (localInstruction := localInstruction (σ := σ)) (result := result) (cost := cost)
    program (fun _ : Data K => True) (fun data => (ambient, data.2)) (fun data => data.1)
    chosen (by intros; trivial)
    (by
      intro source _ localLabels localExit atLocal data _
      rcases data with ⟨tapes, reg⟩
      simpa only [cost, result, Function.update_eq_self] using
        MachineDrain.drainTrace source (localLabels ()) localExit program (atLocal ())
          tapes (tapes source) ambient reg)
    labels exit atLabels (base, register) trivial
  simpa only [sequence_steps, sequence_result, entry] using run

def execution (chosen : List K) (labels : Label chosen → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atLabels : ∀ l, program (labels l) = instruction chosen labels exit l)
    (base : Tapes K) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨entry chosen labels exit, (ambient, register), base⟩
      (some ⟨exit, (ambient, finalRegister chosen register), finalTapes chosen base⟩)
      (lengthSum chosen base + chosen.length) where
  steps := steps chosen base
  evals_in_steps := trace chosen labels exit program atLabels base ambient register
  steps_le_m := steps_le chosen base

def workTapes {N : Nat} (enumeration : Fin N ≃ K) (output : K) : List K :=
  (List.ofFn (fun i => enumeration i)).filter (fun k => decide (k ≠ output))

@[simp] theorem mem_workTapes {N : Nat} (enumeration : Fin N ≃ K) (output k : K) :
    k ∈ workTapes enumeration output ↔ k ≠ output := by
  have hmem : k ∈ List.ofFn (fun i => enumeration i) := by
    apply List.mem_ofFn.mpr
    exact ⟨enumeration.symm k, enumeration.apply_symm_apply k⟩
  simp [workTapes, hmem]

theorem workTapes_length_le {N : Nat} (enumeration : Fin N ≃ K) (output : K) :
    (workTapes enumeration output).length ≤ N := by
  simpa only [workTapes, List.length_ofFn] using
    List.length_filter_le (fun k => decide (k ≠ output)) (List.ofFn (fun i => enumeration i))

def haltTapes (output : K) (word : List Bool) : Tapes K :=
  fun k => if k = output then word else []

theorem finalTapes_workTapes {N : Nat} (enumeration : Fin N ≃ K) (output : K)
    (base : Tapes K) :
    finalTapes (workTapes enumeration output) base = haltTapes output (base output) := by
  funext k
  rw [finalTapes_apply]
  by_cases h : k = output
  · subst k
    simp [haltTapes]
  · simp [haltTapes, h]

theorem cleanupTrace {N : Nat} (enumeration : Fin N ≃ K) (output : K)
    (labels : Label (workTapes enumeration output) → Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atLabels : ∀ l, program (labels l) =
      instruction (workTapes enumeration output) labels none l)
    (base : Tapes K) (ambient : σ) :
    (advance (TM2.step program))^[steps (workTapes enumeration output) base]
      (some ⟨entry (workTapes enumeration output) labels none, (ambient, none), base⟩) =
    some ⟨none, (ambient, none), haltTapes output (base output)⟩ := by
  simpa only [finalRegister_none, finalTapes_workTapes] using
    trace (workTapes enumeration output) labels none program atLabels base ambient none

end DFVSGames.Foundations.Complexity.MachineDrainMany

end OAI
