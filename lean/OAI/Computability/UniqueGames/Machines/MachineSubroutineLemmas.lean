import OAI.Computability.UniqueGames.Foundations.PinskerLemmas
import OAI.Computability.UniqueGames.Machines.MachineCompositionLemmas
import OAI.Computability.UniqueGames.Model

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.Complexity.MachineSubroutine

open Turing

variable {K Λ Λ' σ : Type} {Γ : K → Type}

def label (labels : Λ → Λ') (exit : Option Λ') : Option Λ → Option Λ'
  | none => exit
  | some l => some (labels l)

def configuration (labels : Λ → Λ') (exit : Option Λ') (c : TM2.Cfg Γ Λ σ) :
    TM2.Cfg Γ Λ' σ := ⟨label labels exit c.l, c.var, c.stk⟩

def statement (labels : Λ → Λ') (exit : Option Λ') :
    TM2.Stmt Γ Λ σ → TM2.Stmt Γ Λ' σ
  | .push k f next => .push k f (statement labels exit next)
  | .peek k f next => .peek k f (statement labels exit next)
  | .pop k f next => .pop k f (statement labels exit next)
  | .load f next => .load f (statement labels exit next)
  | .branch f yes no => .branch f (statement labels exit yes) (statement labels exit no)
  | .goto f => .goto (fun s => labels (f s))
  | .halt => match exit with
      | none => .halt
      | some l => .goto (fun _ => l)

variable [DecidableEq K]

theorem stepAux_simulation (labels : Λ → Λ') (exit : Option Λ')
    (q : TM2.Stmt Γ Λ σ) (state : σ) (tapes : ∀ k, List (Γ k)) :
    TM2.stepAux (statement labels exit q) state tapes =
      configuration labels exit (TM2.stepAux q state tapes) := by
  induction q generalizing state tapes with
  | push k f next ih =>
      simpa only [statement, TM2.stepAux] using
        ih state (Function.update tapes k (f state :: tapes k))
  | peek k f next ih =>
      simpa only [statement, TM2.stepAux] using ih (f state (tapes k).head?) tapes
  | pop k f next ih =>
      simpa only [statement, TM2.stepAux] using
        ih (f state (tapes k).head?) (Function.update tapes k (tapes k).tail)
  | load f next ih => simpa only [statement, TM2.stepAux] using ih (f state) tapes
  | branch f yes no ihYes ihNo =>
      cases h : f state with
      | false => simpa only [statement, TM2.stepAux, h, Bool.cond_false] using ihNo state tapes
      | true => simpa only [statement, TM2.stepAux, h, Bool.cond_true] using ihYes state tapes
  | goto f => rfl
  | halt => cases exit <;> rfl

theorem step_simulation (labels : Λ → Λ') (exit : Option Λ')
    (source : Λ → TM2.Stmt Γ Λ σ) (target : Λ' → TM2.Stmt Γ Λ' σ)
    (atLabels : ∀ l, target (labels l) = statement labels exit (source l))
    (a b : TM2.Cfg Γ Λ σ) (h : TM2.step source a = some b) :
    TM2.step target (configuration labels exit a) =
      some (configuration labels exit b) := by
  cases a with
  | mk l state tapes =>
      cases l with
      | none => simp [TM2.step] at h
      | some l =>
          have hb : TM2.stepAux (source l) state tapes = b := Option.some.inj h
          rw [← hb]
          change some (TM2.stepAux (target (labels l)) state tapes) = _
          rw [atLabels, stepAux_simulation]

theorem trace (labels : Λ → Λ') (exit : Option Λ')
    (source : Λ → TM2.Stmt Γ Λ σ) (target : Λ' → TM2.Stmt Γ Λ' σ)
    (atLabels : ∀ l, target (labels l) = statement labels exit (source l))
    (steps : Nat) (a b : TM2.Cfg Γ Λ σ)
    (run : (MachineComposition.advance (TM2.step source))^[steps] (some a) = some b) :
    (MachineComposition.advance (TM2.step target))^[steps]
      (some (configuration labels exit a)) = some (configuration labels exit b) :=
  MachineComposition.liftSuccessfulTrace (TM2.step source) (TM2.step target)
    (configuration labels exit) (step_simulation labels exit source target atLabels) steps a b run

def execution (labels : Λ → Λ') (exit : Option Λ')
    (source : Λ → TM2.Stmt Γ Λ σ) (target : Λ' → TM2.Stmt Γ Λ' σ)
    (atLabels : ∀ l, target (labels l) = statement labels exit (source l))
    {a b : TM2.Cfg Γ Λ σ} {budget : Nat}
    (run : StateTransition.EvalsToInTime (TM2.step source) a (some b) budget) :
    StateTransition.EvalsToInTime (TM2.step target)
      (configuration labels exit a) (some (configuration labels exit b)) budget :=
  MachineComposition.liftExecutionInTime (TM2.step source) (TM2.step target)
    (configuration labels exit) (step_simulation labels exit source target atLabels) run

end UniqueGamesTheorem.Foundations.Complexity.MachineSubroutine

end

section

namespace UniqueGamesTheorem.Foundations.Complexity.MachineStateFrame

open Turing

variable {K Λ Λ' σ τ : Type} {Γ : K → Type}

/-- Same code and stacks, with an untouched caller-register component. -/
def frameStatement : TM2.Stmt Γ Λ σ → TM2.Stmt Γ Λ (σ × τ)
  | .push k f next => .push k (fun state => f state.1) (frameStatement next)
  | .peek k f next => .peek k (fun state bit => (f state.1 bit, state.2))
      (frameStatement next)
  | .pop k f next => .pop k (fun state bit => (f state.1 bit, state.2))
      (frameStatement next)
  | .load f next => .load (fun state => (f state.1, state.2)) (frameStatement next)
  | .branch f yes no => .branch (fun state => f state.1)
      (frameStatement yes) (frameStatement no)
  | .goto f => .goto (fun state => f state.1)
  | .halt => .halt

def frameConfiguration (ambient : τ) (c : TM2.Cfg Γ Λ σ) : TM2.Cfg Γ Λ (σ × τ) :=
  ⟨c.l, (c.var, ambient), c.stk⟩

def frameProgram (source : Λ → TM2.Stmt Γ Λ σ) : Λ → TM2.Stmt Γ Λ (σ × τ) :=
  fun label => frameStatement (source label)

@[simp] theorem frameConfiguration_state (ambient : τ) (c : TM2.Cfg Γ Λ σ) :
    (frameConfiguration ambient c).var.1 = c.var := rfl

@[simp] theorem frameConfiguration_metadata (ambient : τ) (c : TM2.Cfg Γ Λ σ) :
    (frameConfiguration ambient c).var.2 = ambient := rfl

@[simp] theorem frameConfiguration_tapes (ambient : τ) (c : TM2.Cfg Γ Λ σ) :
    (frameConfiguration ambient c).stk = c.stk := rfl

theorem frameStatement_pushBound (q : TM2.Stmt Γ Λ σ) :
    Runtime.statementPushBound (frameStatement (τ := τ) q) = Runtime.statementPushBound q := by
  induction q <;> simp_all only [frameStatement, Runtime.statementPushBound]

/-- Optional continuation and labels use the existing subroutine semantics. -/
def statement (labels : Λ → Λ') (exit : Option Λ') (q : TM2.Stmt Γ Λ σ) :
    TM2.Stmt Γ Λ' (σ × τ) :=
  MachineSubroutine.statement labels exit (frameStatement q)

def configuration (labels : Λ → Λ') (exit : Option Λ') (ambient : τ)
    (c : TM2.Cfg Γ Λ σ) : TM2.Cfg Γ Λ' (σ × τ) :=
  MachineSubroutine.configuration labels exit (frameConfiguration ambient c)

@[simp] theorem configuration_state (labels : Λ → Λ') (exit : Option Λ')
    (ambient : τ) (c : TM2.Cfg Γ Λ σ) :
    (configuration labels exit ambient c).var.1 = c.var := rfl

@[simp] theorem configuration_metadata (labels : Λ → Λ') (exit : Option Λ')
    (ambient : τ) (c : TM2.Cfg Γ Λ σ) :
    (configuration labels exit ambient c).var.2 = ambient := rfl

@[simp] theorem configuration_tapes (labels : Λ → Λ') (exit : Option Λ')
    (ambient : τ) (c : TM2.Cfg Γ Λ σ) :
    (configuration labels exit ambient c).stk = c.stk := rfl

theorem statement_pushBound (labels : Λ → Λ') (exit : Option Λ')
    (q : TM2.Stmt Γ Λ σ) :
    Runtime.statementPushBound (statement (τ := τ) labels exit q) =
      Runtime.statementPushBound q := by
  induction q <;> simp_all only [statement, frameStatement,
    MachineSubroutine.statement, Runtime.statementPushBound]
  cases exit <;> rfl

variable [DecidableEq K]

theorem frame_stepAux (q : TM2.Stmt Γ Λ σ) (state : σ) (ambient : τ)
    (tapes : ∀ k, List (Γ k)) :
    TM2.stepAux (frameStatement q) (state, ambient) tapes =
      frameConfiguration ambient (TM2.stepAux q state tapes) := by
  induction q generalizing state tapes with
  | push k f next ih =>
    simpa only [frameStatement, TM2.stepAux] using
      ih state (Function.update tapes k (f state :: tapes k))
  | peek k f next ih =>
    simpa only [frameStatement, TM2.stepAux] using ih (f state (tapes k).head?) tapes
  | pop k f next ih =>
    simpa only [frameStatement, TM2.stepAux] using
      ih (f state (tapes k).head?) (Function.update tapes k (tapes k).tail)
  | load f next ih => simpa only [frameStatement, TM2.stepAux] using ih (f state) tapes
  | branch f yes no ihYes ihNo =>
    cases h : f state with
    | false => simpa only [frameStatement, TM2.stepAux, h, Bool.cond_false] using ihNo state tapes
    | true => simpa only [frameStatement, TM2.stepAux, h, Bool.cond_true] using ihYes state tapes
  | goto f => rfl
  | halt => rfl

/-- This identity also covers the final halted configuration. -/
theorem frame_step (source : Λ → TM2.Stmt Γ Λ σ) (ambient : τ)
    (c : TM2.Cfg Γ Λ σ) :
    TM2.step (frameProgram source) (frameConfiguration ambient c) =
      (TM2.step source c).map (frameConfiguration ambient) := by
  rcases c with ⟨label, state, tapes⟩
  cases label with
  | none => rfl
  | some label =>
    change some (TM2.stepAux (frameStatement (source label)) (state, ambient) tapes) = _
    rw [frame_stepAux]
    rfl

theorem frame_advance (source : Λ → TM2.Stmt Γ Λ σ) (ambient : τ)
    (c : Option (TM2.Cfg Γ Λ σ)) :
    MachineComposition.advance (TM2.step (frameProgram source))
        (c.map (frameConfiguration ambient)) =
      (MachineComposition.advance (TM2.step source) c).map (frameConfiguration ambient) := by
  cases c with
  | none => rfl
  | some c => exact frame_step source ambient c

theorem frame_iterate (source : Λ → TM2.Stmt Γ Λ σ) (ambient : τ)
    (steps : ℕ) (c : Option (TM2.Cfg Γ Λ σ)) :
    (MachineComposition.advance (TM2.step (frameProgram source)))^[steps]
        (c.map (frameConfiguration ambient)) =
      ((MachineComposition.advance (TM2.step source))^[steps] c).map
        (frameConfiguration ambient) := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    exact frame_advance source ambient _

/-- Actual execution with the same step count, budget, and tapes. -/
def frameExecution (source : Λ → TM2.Stmt Γ Λ σ) (ambient : τ)
    {start : TM2.Cfg Γ Λ σ} {finish : Option (TM2.Cfg Γ Λ σ)} {budget : ℕ}
    (run : StateTransition.EvalsToInTime (TM2.step source) start finish budget) :
    StateTransition.EvalsToInTime (TM2.step (frameProgram source))
      (frameConfiguration ambient start) (finish.map (frameConfiguration ambient)) budget where
  steps := run.steps
  evals_in_steps := by
    have h := run.evals_in_steps
    change (MachineComposition.advance (TM2.step source))^[run.steps] (some start) = finish at h
    change (MachineComposition.advance (TM2.step (frameProgram source)))^[run.steps]
      ((some start).map (frameConfiguration ambient)) = finish.map (frameConfiguration ambient)
    rw [frame_iterate, h]
  steps_le_m := run.steps_le_m

@[simp] theorem frameExecution_steps (source : Λ → TM2.Stmt Γ Λ σ) (ambient : τ)
    {start : TM2.Cfg Γ Λ σ} {finish : Option (TM2.Cfg Γ Λ σ)} {budget : ℕ}
    (run : StateTransition.EvalsToInTime (TM2.step source) start finish budget) :
    (frameExecution source ambient run).steps = run.steps := rfl

theorem stepAux_simulation (labels : Λ → Λ') (exit : Option Λ')
    (q : TM2.Stmt Γ Λ σ) (state : σ) (ambient : τ) (tapes : ∀ k, List (Γ k)) :
    TM2.stepAux (statement labels exit q) (state, ambient) tapes =
      configuration labels exit ambient (TM2.stepAux q state tapes) := by
  rw [statement, MachineSubroutine.stepAux_simulation, frame_stepAux]
  rfl

theorem step_simulation (labels : Λ → Λ') (exit : Option Λ') (ambient : τ)
    (source : Λ → TM2.Stmt Γ Λ σ) (target : Λ' → TM2.Stmt Γ Λ' (σ × τ))
    (atLabels : ∀ l, target (labels l) = statement labels exit (source l))
    (a b : TM2.Cfg Γ Λ σ) (h : TM2.step source a = some b) :
    TM2.step target (configuration labels exit ambient a) =
      some (configuration labels exit ambient b) := by
  have framed : TM2.step (frameProgram source) (frameConfiguration ambient a) =
      some (frameConfiguration ambient b) := by
    rw [frame_step, h]
    rfl
  exact MachineSubroutine.step_simulation labels exit (frameProgram source) target
    atLabels _ _ framed

theorem trace (labels : Λ → Λ') (exit : Option Λ') (ambient : τ)
    (source : Λ → TM2.Stmt Γ Λ σ) (target : Λ' → TM2.Stmt Γ Λ' (σ × τ))
    (atLabels : ∀ l, target (labels l) = statement labels exit (source l))
    (steps : ℕ) (a b : TM2.Cfg Γ Λ σ)
    (run : (MachineComposition.advance (TM2.step source))^[steps] (some a) = some b) :
    (MachineComposition.advance (TM2.step target))^[steps]
      (some (configuration labels exit ambient a)) = some (configuration labels exit ambient b) :=
  MachineComposition.liftSuccessfulTrace (TM2.step source) (TM2.step target)
    (configuration labels exit ambient) (step_simulation labels exit ambient source target atLabels)
    steps a b run

def execution (labels : Λ → Λ') (exit : Option Λ') (ambient : τ)
    (source : Λ → TM2.Stmt Γ Λ σ) (target : Λ' → TM2.Stmt Γ Λ' (σ × τ))
    (atLabels : ∀ l, target (labels l) = statement labels exit (source l))
    {a b : TM2.Cfg Γ Λ σ} {budget : ℕ}
    (run : StateTransition.EvalsToInTime (TM2.step source) a (some b) budget) :
    StateTransition.EvalsToInTime (TM2.step target)
      (configuration labels exit ambient a) (some (configuration labels exit ambient b)) budget :=
  MachineComposition.liftExecutionInTime (TM2.step source) (TM2.step target)
    (configuration labels exit ambient) (step_simulation labels exit ambient source target atLabels) run

@[simp] theorem execution_steps (labels : Λ → Λ') (exit : Option Λ') (ambient : τ)
    (source : Λ → TM2.Stmt Γ Λ σ) (target : Λ' → TM2.Stmt Γ Λ' (σ × τ))
    (atLabels : ∀ l, target (labels l) = statement labels exit (source l))
    {a b : TM2.Cfg Γ Λ σ} {budget : ℕ}
    (run : StateTransition.EvalsToInTime (TM2.step source) a (some b) budget) :
    (execution labels exit ambient source target atLabels run).steps = run.steps := rfl

end UniqueGamesTheorem.Foundations.Complexity.MachineStateFrame

end

section

/-!
Concrete finite-alphabet serialization primitives. A natural word `n` is `n`
one-bits followed by a zero delimiter. These are size and decoding theorems, not
running-time certificates. In particular, output length is never called runtime.
-/

namespace UniqueGamesTheorem.Foundations.Complexity

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
  [formula.variables, formula.clauses.length] ++ formula.clauses.flatMap clauseWords

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
      formula.variables + formula.clauses.length + 2 +
        formula.clauses.length * (3 * (formula.variables + 2)) := by
  have h := clausesBits_length_le formula.clauses
  simp only [formulaBits, formulaWords, encodeWords_append, List.length_append,
    encodeWords, encodeWord_length, List.length_nil]
  omega

end UniqueGamesTheorem.Foundations.Complexity

end

section

/-! A checked parser for the concrete 3CNF serialization, including finite-index
bounds, Boolean signs, clause count, and absence of trailing garbage. -/

namespace UniqueGamesTheorem.Foundations.Complexity

open Target

def parseLiteral («variables» : Nat) : List Nat → Option (Literal «variables» × List Nat)
  | index :: sign :: rest =>
      if bounded : index < «variables» then
        if sign = 0 then some (⟨⟨index, bounded⟩, false⟩, rest)
        else if sign = 1 then some (⟨⟨index, bounded⟩, true⟩, rest)
        else none
      else none
  | _ => none

@[simp] theorem parseLiteral_encoded {n : Nat} (literal : Literal n) (rest : List Nat) :
    parseLiteral n (literalWords literal ++ rest) = some (literal, rest) := by
  cases literal with
  | mk index positive =>
      cases positive <;> simp [literalWords, parseLiteral, index.isLt]

def parseClause («variables» : Nat) (words : List Nat) : Option (Clause «variables» × List Nat) := do
  let (a, words) ← parseLiteral «variables» words
  let (b, words) ← parseLiteral «variables» words
  let (c, words) ← parseLiteral «variables» words
  return (⟨#[a, b, c], rfl⟩, words)

theorem clause_three_entries {n : Nat} (clause : Clause n) :
    (⟨#[clause[0], clause[1], clause[2]], rfl⟩ : Clause n) = clause := by
  apply Vector.ext
  intro i hi
  have cases_i : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases cases_i with rfl | rfl | rfl <;> rfl

@[simp] theorem parseClause_encoded {n : Nat} (clause : Clause n) (rest : List Nat) :
    parseClause n (clauseWords clause ++ rest) = some (clause, rest) := by
  simp [clauseWords, List.append_assoc, parseClause, parseLiteral_encoded,
    clause_three_entries]

def parseClauses («variables» : Nat) : Nat → List Nat → Option (List (Clause «variables») × List Nat)
  | 0, words => some ([], words)
  | count + 1, words => do
      let (clause, words) ← parseClause «variables» words
      let (clauses, words) ← parseClauses «variables» count words
      return (clause :: clauses, words)

@[simp] theorem parseClauses_encoded {n : Nat} (clauses : List (Clause n)) (rest : List Nat) :
    parseClauses n clauses.length (clauses.flatMap clauseWords ++ rest) = some (clauses, rest) := by
  induction clauses with
  | nil => rfl
  | cons clause clauses ih =>
      simp [List.append_assoc, parseClauses, parseClause_encoded, ih]

def decodeFormulaWords : List Nat → Option Formula
  | «variables» :: count :: words => do
      let (clauses, trailing) ← parseClauses «variables» count words
      if trailing = [] then some ⟨«variables», clauses⟩ else none
  | _ => none

@[simp] theorem decodeFormulaWords_encoded (formula : Formula) :
    decodeFormulaWords (formulaWords formula) = some formula := by
  cases formula with
  | mk «variables» clauses =>
      have parsed := parseClauses_encoded clauses []
      simp only [List.append_nil] at parsed
      simp [decodeFormulaWords, formulaWords, parsed]

def decodeFormulaBits (bits : List Bool) : Option Formula :=
  decodeWords bits >>= decodeFormulaWords

@[simp] theorem decodeFormulaBits_encoded (formula : Formula) :
    decodeFormulaBits (formulaBits formula) = some formula := by
  simp [decodeFormulaBits, formulaBits]

theorem formulaBits_injective {first second : Formula}
    (same : formulaBits first = formulaBits second) : first = second := by
  have parsed := congrArg decodeFormulaBits same
  simpa only [decodeFormulaBits_encoded, Option.some.injEq] using parsed

end UniqueGamesTheorem.Foundations.Complexity

end

section

/-! Concrete forward-table serialization of unique games. The parser reconstructs
an inverse by finite search and checks both inverse laws. Constraint occurrences,
including repeated parallel edges, are preserved in their original list order. -/

namespace UniqueGamesTheorem.Foundations.Complexity

open Target

def parseLabel (alphabet value : Nat) : Option (Fin alphabet) :=
  if bounded : value < alphabet then some ⟨value, bounded⟩ else none

@[simp] theorem parseLabel_value {q : Nat} (label : Fin q) :
    parseLabel q label.val = some label := by simp [parseLabel, label.isLt]

@[simp] theorem parseLabels_values {q : Nat} (labels : List (Fin q)) :
    (labels.map Fin.val).mapM (parseLabel q) = some labels := by
  induction labels with
  | nil => rfl
  | cons label labels ih => simp [ih]

def parseImages (alphabet : Nat) (words : List Nat) : Option (Vector (Fin alphabet) alphabet) := do
  let labels ← words.mapM (parseLabel alphabet)
  if length_ok : labels.length = alphabet then
    some ⟨labels.toArray, by simpa using length_ok⟩
  else none

@[simp] theorem parseImages_values {q : Nat} (images : Vector (Fin q) q) :
    parseImages q (images.toList.map Fin.val) = some images := by
  unfold parseImages
  rw [parseLabels_values]
  simp
  exact Vector.toArray_toList

def findPreimage {q : Nat} (images : Vector (Fin q) q) (label : Fin q) : Fin q :=
  ((List.finRange q).find? (fun x => decide (images[x] = label))).getD label

theorem findPreimage_permutation {q : Nat} (table : PermutationTable q) (label : Fin q) :
    findPreimage table.images label = table.inverseImages[label] := by
  have exists_preimage :
      ((List.finRange q).find? (fun x => decide (table.images[x] = label))).isSome := by
    apply List.find?_isSome.mpr
    exact ⟨table.inverseImages[label], List.mem_finRange _, by
      simpa only [decide_eq_true_eq] using table.rightInverse label⟩
  cases found : (List.finRange q).find? (fun x => decide (table.images[x] = label)) with
  | none =>
      rw [found] at exists_preimage
      contradiction
  | some x =>
      have image_eq : table.images[x] = label := by
        simpa using List.find?_some found
      have x_eq := table.images_injective (image_eq.trans (table.rightInverse label).symm)
      unfold findPreimage
      rw [found]
      exact x_eq

def searchedInverse {q : Nat} (images : Vector (Fin q) q) : Vector (Fin q) q :=
  Vector.ofFn (findPreimage images)

theorem searchedInverse_permutation {q : Nat} (table : PermutationTable q) :
    searchedInverse table.images = table.inverseImages := by
  apply Vector.ext
  intro i hi
  simpa [searchedInverse] using findPreimage_permutation table ⟨i, hi⟩

def parsePermutation (alphabet : Nat) (words : List Nat) : Option (PermutationTable alphabet) := do
  let images ← parseImages alphabet words
  let inverseImages := searchedInverse images
  if left : ∀ label : Fin alphabet, inverseImages[images[label]] = label then
    if right : ∀ label : Fin alphabet, images[inverseImages[label]] = label then
      some ⟨images, inverseImages, left, right⟩
    else none
  else none

@[simp] theorem parsePermutation_encoded {q : Nat} (table : PermutationTable q) :
    parsePermutation q (tableWords table) = some table := by
  simp only [parsePermutation, tableWords, parseImages_values]
  dsimp only [Bind.bind, Option.bind]
  simp only [searchedInverse_permutation]
  simp only [table.leftInverse, table.rightInverse, implies_true, dite_true]

@[simp] theorem tableWords_length {q : Nat} (table : PermutationTable q) :
    (tableWords table).length = q := by simp [tableWords]

def parseConstraint (vertices alphabet : Nat) :
    List Nat → Option (Constraint vertices alphabet × List Nat)
  | source :: target :: words => do
      let source ← parseLabel vertices source
      let target ← parseLabel vertices target
      let permutation ← parsePermutation alphabet (words.take alphabet)
      return (⟨source, target, permutation⟩, words.drop alphabet)
  | _ => none

@[simp] theorem parseConstraint_encoded {n q : Nat}
    (constraint : Constraint n q) (rest : List Nat) :
    parseConstraint n q (constraintWords constraint ++ rest) = some (constraint, rest) := by
  cases constraint with
  | mk source target permutation =>
      have taken := List.take_left' (l₂ := rest) (tableWords_length permutation)
      have dropped := List.drop_left' (l₂ := rest) (tableWords_length permutation)
      simp [constraintWords, parseConstraint, taken, dropped]

def parseConstraints (vertices alphabet : Nat) :
    Nat → List Nat → Option (List (Constraint vertices alphabet) × List Nat)
  | 0, words => some ([], words)
  | count + 1, words => do
      let (constraint, words) ← parseConstraint vertices alphabet words
      let (constraints, words) ← parseConstraints vertices alphabet count words
      return (constraint :: constraints, words)

@[simp] theorem parseConstraints_encoded {n q : Nat}
    (constraints : List (Constraint n q)) (rest : List Nat) :
    parseConstraints n q constraints.length (constraints.flatMap constraintWords ++ rest) =
      some (constraints, rest) := by
  induction constraints with
  | nil => rfl
  | cons constraint constraints ih =>
      simp [parseConstraints, List.append_assoc, ih]

def decodeGameWords (alphabet : Nat) : List Nat → Option (Instance alphabet)
  | vertices :: encodedAlphabet :: count :: words => do
      if encodedAlphabet = alphabet then
        let (constraints, trailing) ← parseConstraints vertices alphabet count words
        if trailing = [] then
          if nonempty : constraints ≠ [] then some ⟨vertices, constraints, nonempty⟩ else none
        else none
      else none
  | _ => none

@[simp] theorem decodeGameWords_encoded {q : Nat} (game : Instance q) :
    decodeGameWords q (gameWords game) = some game := by
  cases game with
  | mk vertices constraints nonempty =>
      have parsed := parseConstraints_encoded constraints []
      simp only [List.append_nil] at parsed
      simp [decodeGameWords, gameWords, parsed, nonempty]

def decodeGameBits (alphabet : Nat) (bits : List Bool) : Option (Instance alphabet) :=
  decodeWords bits >>= decodeGameWords alphabet

@[simp] theorem decodeGameBits_encoded {q : Nat} (game : Instance q) :
    decodeGameBits q (gameBits game) = some game := by
  simp [decodeGameBits, gameBits]

theorem gameBits_injective {q : Nat} {first second : Instance q}
    (same : gameBits first = gameBits second) : first = second := by
  have parsed := congrArg (decodeGameBits q) same
  simpa only [decodeGameBits_encoded, Option.some.injEq] using parsed

@[simp] theorem constraintWords_length {n q : Nat} (constraint : Constraint n q) :
    (constraintWords constraint).length = q + 2 := by simp [constraintWords]

theorem constraintsWords_length {n q : Nat} (constraints : List (Constraint n q)) :
    (constraints.flatMap constraintWords).length = constraints.length * (q + 2) := by
  induction constraints with
  | nil => simp
  | cons constraint constraints ih =>
      simp only [List.flatMap_cons, List.length_append, constraintWords_length,
        List.length_cons, Nat.add_mul, Nat.one_mul, ih]
      omega

@[simp] theorem gameWords_length {q : Nat} (game : Instance q) :
    (gameWords game).length = 3 + game.constraints.length * (q + 2) := by
  simp only [gameWords, List.length_append, List.length_cons, List.length_nil,
    constraintsWords_length]

end UniqueGamesTheorem.Foundations.Complexity

end

section

/-! The exact input/output codec of the one-orbit postprocessor. Doubling is
only an encoding adapter: no equality of game values under independent labels
on the two copies is asserted. -/

namespace UniqueGamesTheorem.Explicit.MachineSingleOrbitCodec

open UniqueGamesTheorem.Foundations.Target UniqueGamesTheorem.Foundations.Complexity

def doubleConstraint {n q : Nat} (c : Constraint n q) : Constraint (2 * n) q where
  source := ⟨c.source.val, by have := c.source.isLt; omega⟩
  target := ⟨n + c.target.val, by have := c.target.isLt; omega⟩
  permutation := c.permutation

def doubleInstance {q : Nat} (I : Instance q) : Instance q where
  vertices := 2 * I.vertices
  constraints := I.constraints.map doubleConstraint
  nonempty h := I.nonempty (List.map_eq_nil_iff.mp h)

def rowBits {n q : Nat} (c : Constraint n q) : List Bool :=
  encodeWords (constraintWords c)

def doubledRowBits {n q : Nat} (c : Constraint n q) : List Bool :=
  encodeWords (constraintWords (doubleConstraint c))

def rowsBits {n q : Nat} (cs : List (Constraint n q)) : List Bool :=
  encodeWords (cs.flatMap constraintWords)

def doubledRowsBits {n q : Nat} (cs : List (Constraint n q)) : List Bool :=
  encodeWords (cs.flatMap (fun c => constraintWords (doubleConstraint c)))

@[simp] theorem rowBits_eq {n q : Nat} (c : Constraint n q) :
    rowBits c = encodeWord c.source.val ++ encodeWord c.target.val ++
      encodeWords (tableWords c.permutation) := by
  simp [rowBits, constraintWords, encodeWords, List.append_assoc]

@[simp] theorem doubledRowBits_eq {n q : Nat} (c : Constraint n q) :
    doubledRowBits c = encodeWord c.source.val ++ encodeWord (n + c.target.val) ++
      encodeWords (tableWords c.permutation) := by
  simp [doubledRowBits, constraintWords, doubleConstraint, encodeWords, List.append_assoc]

@[simp] theorem rowsBits_nil {n q : Nat} : rowsBits ([] : List (Constraint n q)) = [] := rfl
@[simp] theorem doubledRowsBits_nil {n q : Nat} :
    doubledRowsBits ([] : List (Constraint n q)) = [] := rfl

@[simp] theorem rowsBits_cons {n q : Nat} (c : Constraint n q) (cs : List (Constraint n q)) :
    rowsBits (c :: cs) = rowBits c ++ rowsBits cs := by
  simp [rowsBits, rowBits]

@[simp] theorem doubledRowsBits_cons {n q : Nat} (c : Constraint n q)
    (cs : List (Constraint n q)) :
    doubledRowsBits (c :: cs) = doubledRowBits c ++ doubledRowsBits cs := by
  simp [doubledRowsBits, doubledRowBits]

theorem gameBits_eq {q : Nat} (I : Instance q) :
    gameBits I = encodeWord I.vertices ++ encodeWord q ++
      encodeWord I.constraints.length ++ rowsBits I.constraints := by
  simp [gameBits, gameWords, encodeWords, rowsBits, List.append_assoc]

theorem doubled_gameBits_eq {q : Nat} (I : Instance q) :
    gameBits (doubleInstance I) = encodeWord (2 * I.vertices) ++ encodeWord q ++
      encodeWord I.constraints.length ++ doubledRowsBits I.constraints := by
  simp [gameBits, gameWords, doubleInstance, encodeWords, doubledRowsBits,
    List.flatMap_map, List.append_assoc]

theorem input_length_eq {q : Nat} (I : Instance q) :
    (gameBits (doubleInstance I)).length =
      2 * I.vertices + q + I.constraints.length + 3 +
        (doubledRowsBits I.constraints).length := by
  rw [doubled_gameBits_eq]
  simp only [List.length_append, encodeWord_length]
  omega

theorem vertices_le_input_length {q : Nat} (I : Instance q) :
    I.vertices ≤ (gameBits (doubleInstance I)).length := by
  rw [input_length_eq]
  omega

theorem rows_le_input_length {q : Nat} (I : Instance q) :
    I.constraints.length ≤ (gameBits (doubleInstance I)).length := by
  rw [input_length_eq]
  omega

end UniqueGamesTheorem.Explicit.MachineSingleOrbitCodec

end

end OAI
