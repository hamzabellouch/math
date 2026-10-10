import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Basic
import OAI.Computability.PerfectCompleteness.Machines.CircuitEncodingLemmas
import OAI.Computability.UniqueGames.Machines.MachineUnaryAffineAt

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.Complexity.CookLevin.TransitionTemplate

inductive Position where
  | current
  | zero
  | succ (p : Position)
  | pred (p : Position)
  deriving DecidableEq

def Position.eval (cursor : Nat) : Position → Nat
  | .current => cursor
  | .zero => 0
  | .succ p => p.eval cursor + 1
  | .pred p => p.eval cursor - 1

end UniqueGamesTheorem.Foundations.Complexity.CookLevin.TransitionTemplate

end

section

namespace UniqueGamesTheorem.Foundations.Complexity.CookLevin.PositionMachine

open Turing MachineComposition TransitionTemplate

def usesCurrent : Position → Bool
  | .current => true
  | .zero => false
  | .succ p => usesCurrent p
  | .pred p => usesCurrent p

def initialValue (p : Position) (cursor : Nat) : Nat :=
  if usesCurrent p then cursor else 0

def transform : Position → Nat → Nat
  | .current, n => n
  | .zero, n => n
  | .succ p, n => transform p n + 1
  | .pred p, n => transform p n - 1

theorem transform_initialValue (p : Position) (cursor : Nat) :
    transform p (initialValue p cursor) = p.eval cursor := by
  induction p with
  | current => rfl
  | zero => rfl
  | succ p ih =>
    change transform p (initialValue p cursor) + 1 = p.eval cursor + 1
    exact congrArg (fun n : Nat => n + 1) ih
  | pred p ih =>
    change transform p (initialValue p cursor) - 1 = p.eval cursor - 1
    exact congrArg (fun n : Nat => n - 1) ih

section Statements

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool
abbrev State (σ : Type) := σ × Option Bool

def decrement (destination : K)
    (continuation : TM2.Stmt (Alphabet (K := K)) Λ (State σ)) :
    TM2.Stmt (Alphabet (K := K)) Λ (State σ) :=
  .peek destination (fun s head => (s.1, head))
    (.branch (fun s => s.2.getD false)
      (.pop destination (fun s _ => (s.1, none)) continuation)
      (.load (fun s => (s.1, none)) continuation))

theorem stepAux_decrement (destination : K)
    (continuation : TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (base : K → List Bool) (n : Nat) (suffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    TM2.stepAux (decrement destination continuation) (ambient, register)
      (Function.update base destination (encodeWord n ++ suffix)) =
      TM2.stepAux continuation (ambient, none)
        (Function.update base destination (encodeWord (n - 1) ++ suffix)) := by
  cases n <;> simp [decrement, TM2.stepAux, encodeWord, List.replicate_succ]

def suffixStatement (destination : K) : Position →
    TM2.Stmt (Alphabet (K := K)) Λ (State σ) →
      TM2.Stmt (Alphabet (K := K)) Λ (State σ)
  | .current, continuation => .load (fun s => (s.1, none)) continuation
  | .zero, continuation => .load (fun s => (s.1, none)) continuation
  | .succ p, continuation =>
      suffixStatement destination p (.push destination (fun _ => true) continuation)
  | .pred p, continuation => suffixStatement destination p (decrement destination continuation)

theorem stepAux_suffixStatement (destination : K) (p : Position)
    (continuation : TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (base : K → List Bool) (n : Nat) (suffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    TM2.stepAux (suffixStatement destination p continuation) (ambient, register)
      (Function.update base destination (encodeWord n ++ suffix)) =
      TM2.stepAux continuation (ambient, none)
        (Function.update base destination (encodeWord (transform p n) ++ suffix)) := by
  induction p generalizing continuation with
  | current => rfl
  | zero => rfl
  | succ p ih =>
    rw [suffixStatement, ih]
    simp [TM2.stepAux, transform, encodeWord, List.replicate_succ]
  | pred p ih =>
    rw [suffixStatement, ih, stepAux_decrement]
    rfl

inductive Label where
  | start
  | scan
  | restore
  | finish
  deriving DecidableEq

instance : Fintype Label where
  elems := { .start, .scan, .restore, .finish }
  complete l := by cases l <;> simp

def statement (source scratch destination : K) (p : Position)
    (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt (Alphabet (K := K)) Λ (State σ)
  | .start => if usesCurrent p then
      MachineUnaryAffineAt.seed destination 0 (labels .scan)
      else .push destination (fun _ => false) (.goto fun _ => labels .finish)
  | .scan => MachineUnaryAffineAt.scan source scratch destination 1
      (labels .scan) (labels .restore)
  | .restore => Reduction.MachineTransfer.loopAt scratch source id false
      (labels .restore) (some (labels .finish))
  | .finish => suffixStatement destination p (Reduction.MachineTransfer.exitAt destination exit)

def seedSteps (p : Position) (cursor : Nat) : Nat :=
  if usesCurrent p then 2 * (cursor + 1) + 1 else 1

def steps (p : Position) (cursor : Nat) : Nat := seedSteps p cursor + 1

theorem seedTrace (source scratch destination : K)
    (hs : source ≠ scratch) (hd : source ≠ destination) (hsd : scratch ≠ destination)
    (p : Position) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ l, program (labels l) = statement source scratch destination p labels exit l)
    (base : K → List Bool) (cursor : Nat) (suffix : List Bool)
    (sourceWord : base source = encodeWord cursor ++ suffix) (scratchEmpty : base scratch = [])
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[seedSteps p cursor]
      (some ⟨some (labels .start), (ambient, register), base⟩) =
      some ⟨some (labels .finish), (ambient, if usesCurrent p then none else register),
        Function.update base destination (encodeWord (initialValue p cursor) ++ base destination)⟩ := by
  cases hc : usesCurrent p with
  | false =>
    simp only [seedSteps, initialValue, hc, Bool.false_eq_true, ↓reduceIte,
      Function.iterate_one, advance_some]
    change some (TM2.stepAux (program (labels .start)) (ambient, register) base) = _
    rw [atLabels]
    simp [statement, hc, TM2.stepAux, encodeWord]
  | true =>
    have h := MachineUnaryAffineAt.seededAffineTrace source scratch destination hs hd hsd
      1 0 (labels .start) (labels .scan) (labels .restore) (some (labels .finish))
      program (by simpa [statement, hc] using atLabels .start)
      (atLabels .scan) (atLabels .restore) base cursor suffix sourceWord scratchEmpty
      ambient register
    simpa only [seedSteps, initialValue, hc, ↓reduceIte, one_mul, add_zero] using h

theorem finishTrace (source scratch destination : K)
    (p : Position) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atFinish : program (labels .finish) = statement source scratch destination p labels exit .finish)
    (base : K → List Bool) (n : Nat) (suffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[1]
      (some ⟨some (labels .finish), (ambient, register),
        Function.update base destination (encodeWord n ++ suffix)⟩) =
      some ⟨exit, (ambient, none),
        Function.update base destination (encodeWord (transform p n) ++ suffix)⟩ := by
  change some (TM2.stepAux (program (labels .finish)) _ _) = _
  rw [atFinish, statement, stepAux_suffixStatement]
  cases exit <;> rfl

theorem positionTrace (source scratch destination : K)
    (hs : source ≠ scratch) (hd : source ≠ destination) (hsd : scratch ≠ destination)
    (p : Position) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ l, program (labels l) = statement source scratch destination p labels exit l)
    (base : K → List Bool) (cursor : Nat) (suffix : List Bool)
    (sourceWord : base source = encodeWord cursor ++ suffix) (scratchEmpty : base scratch = [])
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[steps p cursor]
      (some ⟨some (labels .start), (ambient, register), base⟩) =
      some ⟨exit, (ambient, none),
        Function.update base destination (encodeWord (p.eval cursor) ++ base destination)⟩ := by
  rw [steps, Nat.add_comm (seedSteps p cursor) 1, Function.iterate_add_apply,
    seedTrace source scratch destination hs hd hsd p labels exit program atLabels
      base cursor suffix sourceWord scratchEmpty ambient register,
    finishTrace source scratch destination p labels exit program (atLabels .finish),
    transform_initialValue]

noncomputable def timePolynomial : Polynomial Nat := Polynomial.C 2 * Polynomial.X + Polynomial.C 4

theorem steps_le_time (p : Position) (cursor : Nat) :
    steps p cursor ≤ timePolynomial.eval cursor := by
  simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, steps, seedSteps]
  split <;> omega

def positionInPolynomialTime (source scratch destination : K)
    (hs : source ≠ scratch) (hd : source ≠ destination) (hsd : scratch ≠ destination)
    (p : Position) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ l, program (labels l) = statement source scratch destination p labels exit l)
    (base : K → List Bool) (cursor : Nat) (suffix : List Bool)
    (sourceWord : base source = encodeWord cursor ++ suffix) (scratchEmpty : base scratch = [])
    (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels .start), (ambient, register), base⟩
      (some ⟨exit, (ambient, none),
        Function.update base destination (encodeWord (p.eval cursor) ++ base destination)⟩)
      (timePolynomial.eval cursor) where
  steps := steps p cursor
  evals_in_steps := positionTrace source scratch destination hs hd hsd p labels exit
    program atLabels base cursor suffix sourceWord scratchEmpty ambient register
  steps_le_m := steps_le_time p cursor

end Statements

abbrev machine (p : Position) : Turing.FinTM2 where
  K := Fin 3
  k₀ := 0
  k₁ := 2
  Γ _ := Bool
  Λ := Label
  main := .start
  σ := State Unit
  initialState := ((), none)
  m := statement 0 1 2 p id none

def machineInPolynomialTime (p : Position) (base : Fin 3 → List Bool)
    (cursor : Nat) (suffix : List Bool)
    (sourceWord : base 0 = encodeWord cursor ++ suffix) (scratchEmpty : base 1 = []) :
    StateTransition.EvalsToInTime (machine p).step
      ⟨some .start, ((), none), base⟩
      (some ⟨none, ((), none), Function.update base 2 (encodeWord (p.eval cursor) ++ base 2)⟩)
      (timePolynomial.eval cursor) :=
  positionInPolynomialTime 0 1 2 (by decide) (by decide) (by decide) p id none
    (statement 0 1 2 p id none) (fun _ => rfl) base cursor suffix sourceWord scratchEmpty () none

end UniqueGamesTheorem.Foundations.Complexity.CookLevin.PositionMachine

end

section

namespace UniqueGamesTheorem.Foundations.Complexity.CookLevin.PostfixModel

inductive Token where
  | const (value : Bool)
  | not | and | or
  | input (wire : Nat)
  deriving DecidableEq

namespace Token

def tag : Token → Fin 6
  | .const false => 0
  | .const true => 1
  | .not => 2
  | .and => 3
  | .or => 4
  | .input _ => 5

def words : Token → List Nat
  | .const false => [0]
  | .const true => [1]
  | .not => [2]
  | .and => [3]
  | .or => [4]
  | .input wire => [5, wire]

def bits (token : Token) : List Bool := encodeWords token.words

def takeGate : Token → List Nat → Option (Gate × List Nat)
  | .const value, roots => some (.const value, roots)
  | .input wire, roots => some (.or wire wire, roots)
  | .not, arg :: roots => some (.not arg, roots)
  | .and, right :: left :: roots => some (.and left right, roots)
  | .or, right :: left :: roots => some (.or left right, roots)
  | _, _ => none

end Token

def tokenWords (tokens : List Token) : List Nat := tokens.flatMap Token.words
def tokenBits (tokens : List Token) : List Bool := encodeWords (tokenWords tokens)

def compileTokens (start : Nat) (roots : List Nat) :
    List Token → Option (Nat × List Nat × List Gate)
  | [] => some (start, roots, [])
  | token :: tokens => do
      let (gate, remaining) ← token.takeGate roots
      let (next, finalRoots, gates) ← compileTokens (start + 1) (start :: remaining) tokens
      pure (next, finalRoots, gate :: gates)

def inputBits (start : Nat) (tokens : List Token) : List Bool :=
  encodeWords [start, tokens.length] ++ tokenBits tokens

end UniqueGamesTheorem.Foundations.Complexity.CookLevin.PostfixModel

end

section

namespace UniqueGamesTheorem.Foundations.Complexity.CookLevin.InitializationTemplate

open PostfixModel

def forTokens : Nat → (Nat → List Token) → List Token
  | 0, _ => []
  | count + 1, body => forTokens count body ++ body count

theorem forTokens_eq_flatMap_range (count : Nat) (body : Nat → List Token) :
    forTokens count body = (List.range count).flatMap body := by
  induction count with
  | zero => rfl
  | succ count ih => simp [forTokens, List.range_succ, ih]

theorem forTokens_eq_ofFn (count : Nat) (body : Nat → List Token) :
    forTokens count body = (List.ofFn fun i : Fin count => body i.val).flatten := by
  induction count with
  | zero => simp [forTokens]
  | succ count ih =>
    rw [forTokens, ih, List.ofFn_succ']
    simp [List.concat_eq_append]

theorem forTokens_succ_first (count : Nat) (body : Nat → List Token) :
    forTokens (count + 1) body = body 0 ++ forTokens count (fun j => body (j + 1)) := by
  simp [forTokens_eq_flatMap_range, List.range_succ_eq_map, List.flatMap_map]

theorem forTokens_congr (count : Nat) (first second : Nat → List Token)
    (h : ∀ i, i < count → first i = second i) :
    forTokens count first = forTokens count second := by
  induction count with
  | zero => rfl
  | succ count ih =>
    rw [forTokens, forTokens, ih (fun i hi => h i (by omega)), h count (by omega)]

theorem forTokens_length_le (count : Nat) (body : Nat → List Token) (cost : Nat)
    (h : ∀ i, i < count → (body i).length ≤ cost) :
    (forTokens count body).length ≤ count * cost := by
  induction count with
  | zero => simp [forTokens]
  | succ count ih =>
    have hp := ih (fun i hi => h i (by omega))
    have hl := h count (by omega)
    simp only [forTokens, List.length_append, Nat.succ_mul]
    omega

theorem forTokens_length_eq (count : Nat) (body : Nat → List Token) (cost : Nat)
    (h : ∀ i, i < count → (body i).length = cost) :
    (forTokens count body).length = count * cost := by
  induction count with
  | zero => simp [forTokens]
  | succ count ih =>
    rw [forTokens, List.length_append, ih (fun i hi => h i (by omega)), h count (by omega)]
    exact (Nat.succ_mul count cost).symm

def closeOr (count : Nat) : List Token := [.const false] ++ List.replicate count .or

def nonemptyTokens (q : Nat) : List Token :=
  forTokens (q + 1) (fun i => [.input i]) ++ closeOr (q + 1)

def clashPairTokens (i j : Nat) : List Token :=
  if i = j then [.const false] else [.input i, .input j, .and]

def clashRowTokens (q i : Nat) : List Token :=
  forTokens (q + 1) (clashPairTokens i) ++ closeOr (q + 1)

def clashTokens (q : Nat) : List Token :=
  forTokens (q + 1) (clashRowTokens q) ++ closeOr (q + 1)

def validityTokens (q : Nat) : List Token :=
  nonemptyTokens q ++ clashTokens q ++ [.not, .and]

def presenceTokens (q n : Nat) : List Token :=
  forTokens (q + 1) (fun length => [.input length, .const (decide (n < length)), .and]) ++
    closeOr (q + 1)

def selectorLoopTokens (count start threshold : Nat) : List Token :=
  forTokens count (fun j => [.input (start + j), .const (decide (threshold ≤ j)), .and])

theorem threshold_zero_iff (threshold used : Nat) :
    threshold - used = 0 ↔ threshold ≤ used := Nat.sub_eq_zero_iff_le

theorem selectorLoopTokens_length (count start threshold : Nat) :
    (selectorLoopTokens count start threshold).length = 3 * count := by
  simpa only [selectorLoopTokens, Nat.mul_comm] using
    forTokens_length_eq count
      (fun j => [.input (start + j), .const (decide (threshold ≤ j)), .and]) 3
      (fun _ _ => rfl)

theorem selectorLoopTokens_succ (count start threshold : Nat) :
    selectorLoopTokens (count + 1) start threshold =
      [.input start, .const (decide (threshold = 0)), .and] ++
        selectorLoopTokens count (start + 1) (threshold - 1) := by
  rw [selectorLoopTokens, forTokens_succ_first]
  simp only [Nat.add_zero, Nat.le_zero]
  apply congrArg (List.append [Token.input start, Token.const (decide (threshold = 0)), Token.and])
  apply forTokens_congr
  intro j _
  have ha : start + (j + 1) = start + 1 + j := by omega
  have ht : (threshold ≤ j + 1) = (threshold - 1 ≤ j) := propext (by omega)
  simp only [ha, ht]

theorem selectorLoopTokens_presence (q n : Nat) :
    selectorLoopTokens (q + 1) 0 (n + 1) ++ closeOr (q + 1) = presenceTokens q n := by
  simp only [selectorLoopTokens, presenceTokens]
  apply congrArg (fun xs : List Token => xs ++ closeOr (q + 1))
  apply forTokens_congr
  intro j _
  simp only [Nat.zero_add, Nat.succ_le_iff]

theorem presenceTokens_length (q n : Nat) : (presenceTokens q n).length = 4 * (q + 1) + 1 := by
  rw [← selectorLoopTokens_presence q n, List.length_append, selectorLoopTokens_length]
  simp only [closeOr, List.length_append, List.length_cons, List.length_nil, List.length_replicate]
  omega

end UniqueGamesTheorem.Foundations.Complexity.CookLevin.InitializationTemplate

end

end OAI
