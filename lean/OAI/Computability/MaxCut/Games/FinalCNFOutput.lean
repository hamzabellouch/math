import Mathlib
import OAI.Computability.MaxCut.PCP.RoundGap
import OAI.Computability.MaxCut.Games.FinalCNFStream

namespace OAI

/-!
The final machine's complete output stream is the exact serialization of its
actual formula. This identity includes the two size fields, every clause and
literal field, and all unary delimiters. No desired output equality is assumed.
-/

namespace MaxCutGames.Foundations.Complexity.FinalCNFMachine.Program

open PCP PCP.AlphabetTable

def formulaHeader (table : GraphTables.Table) : List Bool :=
  encodeWords [6 * table.vertices + 36864 * table.darts, 40960 * table.darts]

theorem formulaHeader_eq (table : GraphTables.Table) :
    formulaHeader table = encodeWords [(FinalTableFormula.output table).«variables»,
      (FinalTableFormula.output table).clauses.length] := by
  simp only [formulaHeader, FinalTableFormula.variable_count, FinalTableFormula.clause_count,
    Nat.mul_comm]

theorem headerPlan_eq_formulaHeader (table : GraphTables.Table) (tail head row : Nat)
    (ambient : Ambient) :
    headerPlan.flatMap (Emitter.commandBits
      (values table.vertices table.darts tail head row) ambient) = formulaHeader table :=
  headerPlan_bits table.vertices table.darts tail head row ambient

theorem outputStream_eq_clauseBits (table : GraphTables.Table) :
    outputStream rowPlan table (List.finRange table.darts) =
      encodeWords ((FinalTableFormula.output table).clauses.flatMap Complexity.clauseWords) := by
  calc
    _ = (List.finRange table.darts).flatMap (fun e =>
          encodeWords ((VerifierToCNF.eventBlock (FinalCNFPattern.tableVerifier table)
            (by decide) e).flatMap Complexity.clauseWords)) := by
      apply List.flatMap_congr
      intro e he
      exact rowPlan_bits table e
    _ = encodeWords ((List.finRange table.darts).flatMap (fun e =>
          (VerifierToCNF.eventBlock (FinalCNFPattern.tableVerifier table)
            (by decide) e).flatMap Complexity.clauseWords)) :=
      (encodeWords_flatMap _ _).symm
    _ = _ := by
      congr 1
      rw [← List.flatMap_assoc]
      rfl

theorem header_append_outputStream (table : GraphTables.Table) :
    formulaHeader table ++ outputStream rowPlan table (List.finRange table.darts) =
      formulaBits (FinalTableFormula.output table) := by
  rw [formulaHeader_eq, outputStream_eq_clauseBits]
  exact (encodeWords_append _ _).symm

theorem emitted_output_eq (table : GraphTables.Table) (tail head row : Nat)
    (ambient : Ambient) :
    headerPlan.flatMap (Emitter.commandBits
      (values table.vertices table.darts tail head row) ambient) ++
      outputStream rowPlan table (List.finRange table.darts) =
        formulaBits (FinalTableFormula.output table) := by
  rw [headerPlan_eq_formulaHeader]
  exact header_append_outputStream table

/-- Reversing the finished stack accumulator restores the required output order. -/
theorem reversed_accumulator_output (table : GraphTables.Table) :
    (formulaHeader table ++ outputStream rowPlan table (List.finRange table.darts)).reverse.reverse =
      formulaBits (FinalTableFormula.output table) := by
  rw [List.reverse_reverse, header_append_outputStream]

theorem accumulator_length_bound (table : GraphTables.Table) :
    (formulaHeader table ++ outputStream rowPlan table (List.finRange table.darts)).reverse.length ≤
      FinalTableFormula.sizePolynomial.eval (GraphTables.tableBits table).length := by
  rw [List.length_reverse, header_append_outputStream]
  exact FinalTableFormula.formulaBits_length_le_polynomial table

end MaxCutGames.Foundations.Complexity.FinalCNFMachine.Program

namespace MaxCutGames.Foundations.Complexity.FinalCNFMachine.Program

open PCP

noncomputable def rowTimePolynomial : Polynomial Nat :=
  Polynomial.C 860160 * (Polynomial.C 3 * (Polynomial.X + Polynomial.C 1) + Polynomial.C 3) +
    Polynomial.C 12 * Polynomial.X + Polynomial.C 15

theorem rowTimePolynomial_eval (N : Nat) :
    rowTimePolynomial.eval N = rowTime rowPlan N := by
  simp only [rowTimePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, rowTime, rowPlan_length]

theorem rowTime_expanded (N : Nat) : rowTime rowPlan N = 2580492 * N + 5160975 := by
  rw [rowTime, rowPlan_length]
  omega

/-- Header, at most `N` rows with guards, and the final output reversal. -/
noncomputable def phaseTimePolynomial : Polynomial Nat :=
  headerTimePolynomial +
    (Polynomial.X * (rowTimePolynomial + Polynomial.C 1) + Polynomial.C 1) +
    (FinalTableFormula.sizePolynomial + Polynomial.C 1)

theorem phaseTimePolynomial_eval (N : Nat) :
    phaseTimePolynomial.eval N =
      headerTimePolynomial.eval N + (N * (rowTime rowPlan N + 1) + 1) +
        (FinalTableFormula.sizePolynomial.eval N + 1) := by
  simp only [phaseTimePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, rowTimePolynomial_eval]

theorem phaseTimePolynomial_eval_expanded (N : Nat) :
    phaseTimePolynomial.eval N = 4532428812 * N ^ 2 + 5484585 * N + 56 := by
  rw [phaseTimePolynomial_eval, headerTimePolynomial_eval, rowTime_expanded,
    FinalTableFormula.sizePolynomial_eval]
  ring

theorem phaseTime_le {N rows outputLength : Nat} (rowBound : rows ≤ N)
    (outputBound : outputLength ≤ FinalTableFormula.sizePolynomial.eval N) :
    headerTimePolynomial.eval N + (rows * (rowTime rowPlan N + 1) + 1) +
      (outputLength + 1) ≤ phaseTimePolynomial.eval N := by
  have hrows := Nat.mul_le_mul_right (rowTime rowPlan N + 1) rowBound
  rw [phaseTimePolynomial_eval]
  omega

/-- The bound specialized to the actual table and actual formula serialization. -/
theorem table_phaseTime_le (table : GraphTables.Table) :
    headerTimePolynomial.eval (GraphTables.tableBits table).length +
      (table.darts * (rowTime rowPlan (GraphTables.tableBits table).length + 1) + 1) +
      ((formulaBits (FinalTableFormula.output table)).length + 1) ≤
        phaseTimePolynomial.eval (GraphTables.tableBits table).length :=
  phaseTime_le (GraphTables.darts_le_tableBits_length table)
    (FinalTableFormula.formulaBits_length_le_polynomial table)

/-- Twelve private stacks are drained, then the finite state is reset.
`C` is the fixed maximum number of pushes in a raw-program transition. -/
noncomputable def finalTimePolynomial (C : Nat) : Polynomial Nat :=
  phaseTimePolynomial + Polynomial.C 12 *
    (Polynomial.X + phaseTimePolynomial * Polynomial.C C + Polynomial.C 1) + Polynomial.C 1

theorem finalTimePolynomial_eval (C N : Nat) :
    (finalTimePolynomial C).eval N = phaseTimePolynomial.eval N +
      12 * (N + phaseTimePolynomial.eval N * C + 1) + 1 := by
  simp only [finalTimePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X]

/-- Pure budget composition; the drain implementation supplies its own trace. -/
theorem finalTime_le (C N workLength : Nat)
    (workBound : workLength ≤ N + phaseTimePolynomial.eval N * C) :
    phaseTimePolynomial.eval N + 12 * (workLength + 1) + 1 ≤
      (finalTimePolynomial C).eval N := by
  have h := Nat.mul_le_mul_left 12 (Nat.add_le_add_right workBound 1)
  rw [finalTimePolynomial_eval]
  omega

end MaxCutGames.Foundations.Complexity.FinalCNFMachine.Program

namespace MaxCutGames.Foundations.Complexity.FinalCNFCleanup

open Turing MachineComposition
open FinalCNFMachine (State)
open FinalCNFMachine.Program (Tape Plan)

section Redirect

variable {K Λ Λ' σ : Type} {Γ : K → Type} [DecidableEq K]

def redirectLabel (labels : Λ → Λ') (haltTarget : Option Λ') : Option Λ → Option Λ'
  | none => haltTarget
  | some label => some (labels label)

def redirectCfg (labels : Λ → Λ') (haltTarget : Option Λ') (cfg : TM2.Cfg Γ Λ σ) :
    TM2.Cfg Γ Λ' σ :=
  ⟨redirectLabel labels haltTarget cfg.l, cfg.var, cfg.stk⟩

/-- Structural redirection changes only the destinations of goto and halt. -/
def redirectStmt (labels : Λ → Λ') (haltTarget : Option Λ') :
    TM2.Stmt Γ Λ σ → TM2.Stmt Γ Λ' σ
  | .push k f next => .push k f (redirectStmt labels haltTarget next)
  | .peek k f next => .peek k f (redirectStmt labels haltTarget next)
  | .pop k f next => .pop k f (redirectStmt labels haltTarget next)
  | .load f next => .load f (redirectStmt labels haltTarget next)
  | .branch test yes no => .branch test
      (redirectStmt labels haltTarget yes) (redirectStmt labels haltTarget no)
  | .goto label => .goto (fun state => labels (label state))
  | .halt => match haltTarget with
    | none => .halt
    | some label => .goto (fun _ => label)

theorem stepAux_redirect (labels : Λ → Λ') (haltTarget : Option Λ')
    (stmt : TM2.Stmt Γ Λ σ) (state : σ) (tapes : ∀ k, List (Γ k)) :
    TM2.stepAux (redirectStmt labels haltTarget stmt) state tapes =
      redirectCfg labels haltTarget (TM2.stepAux stmt state tapes) := by
  induction stmt generalizing state tapes with
  | push k f next ih => exact ih state (Function.update tapes k (f state :: tapes k))
  | peek k f next ih => exact ih (f state (tapes k).head?) tapes
  | pop k f next ih =>
      exact ih (f state (tapes k).head?) (Function.update tapes k (tapes k).tail)
  | load f next ih => exact ih (f state) tapes
  | branch test yes no ihYes ihNo =>
      cases h : test state with
      | false => simpa only [redirectStmt, TM2.stepAux, h, Bool.cond_false] using ihNo state tapes
      | true => simpa only [redirectStmt, TM2.stepAux, h, Bool.cond_true] using ihYes state tapes
  | goto label => rfl
  | halt => cases haltTarget <;> rfl

end Redirect

/-- The raw machine has thirteen tapes. These are precisely the twelve
non-output tapes, including the original input and retained archive. -/
def chosen : List Tape :=
  [.input, .accumulator, .scratch, .vertices, .darts, .tail, .head,
    .rowIndex, .archive, .reverseIndex, .scanWork, .indexWork]

@[simp] theorem chosen_length : chosen.length = 12 := rfl

@[simp] theorem mem_chosen (tape : Tape) : tape ∈ chosen ↔ tape ≠ .output := by
  cases tape <;> simp [chosen]

abbrev Label (headerPlan rowPlan : Plan) :=
  FinalCNFMachine.Program.Label headerPlan.length rowPlan.length ⊕
    (MachineDrainMany.Label chosen ⊕ Unit)

def cleanupLabel (headerPlan rowPlan : Plan) : MachineDrainMany.Label chosen → Label headerPlan rowPlan :=
  fun label => .inr (.inl label)

def resetLabel (headerPlan rowPlan : Plan) : Label headerPlan rowPlan := .inr (.inr ())

def cleanupEntry (headerPlan rowPlan : Plan) : Option (Label headerPlan rowPlan) :=
  MachineDrainMany.entry chosen (cleanupLabel headerPlan rowPlan) (some (resetLabel headerPlan rowPlan))

def completedProgram (headerPlan rowPlan : Plan) : Label headerPlan rowPlan →
    TM2.Stmt (fun _ : Tape => Bool) (Label headerPlan rowPlan) (State Unit)
  | .inl label => redirectStmt Sum.inl (cleanupEntry headerPlan rowPlan)
      (FinalCNFMachine.Program.program headerPlan rowPlan label)
  | .inr (.inl label) => MachineDrainMany.instruction chosen (cleanupLabel headerPlan rowPlan)
      (some (resetLabel headerPlan rowPlan)) label
  | .inr (.inr _) => .load (fun _ => (FinalCNFMachine.Program.machine headerPlan rowPlan).initialState) .halt

def completedMachine (headerPlan rowPlan : Plan) : FinTM2 where
  K := Tape
  k₀ := .input
  k₁ := .output
  Γ _ := Bool
  Λ := Label headerPlan rowPlan
  main := .inl .copyFirst
  σ := State Unit
  initialState := (FinalCNFMachine.Program.machine headerPlan rowPlan).initialState
  m := completedProgram headerPlan rowPlan

def embeddedCfg (headerPlan rowPlan : Plan)
    (cfg : (FinalCNFMachine.Program.machine headerPlan rowPlan).Cfg) :
    (completedMachine headerPlan rowPlan).Cfg :=
  redirectCfg Sum.inl (cleanupEntry headerPlan rowPlan) cfg

theorem step_simulation (headerPlan rowPlan : Plan)
    (a b : (FinalCNFMachine.Program.machine headerPlan rowPlan).Cfg)
    (step : (FinalCNFMachine.Program.machine headerPlan rowPlan).step a = some b) :
    (completedMachine headerPlan rowPlan).step (embeddedCfg headerPlan rowPlan a) =
      some (embeddedCfg headerPlan rowPlan b) := by
  cases a with
  | mk label state tapes =>
    cases label with
    | none => simp [FinTM2.step, TM2.step] at step
    | some label =>
      have hb : TM2.stepAux (FinalCNFMachine.Program.program headerPlan rowPlan label)
          state tapes = b := Option.some.inj step
      rw [← hb]
      change some (TM2.stepAux
        (redirectStmt Sum.inl (cleanupEntry headerPlan rowPlan)
          (FinalCNFMachine.Program.program headerPlan rowPlan label)) state tapes) = _
      erw [stepAux_redirect]
      rfl

@[simp] theorem embedded_init (headerPlan rowPlan : Plan) (input : List Bool) :
    embeddedCfg headerPlan rowPlan (initList (FinalCNFMachine.Program.machine headerPlan rowPlan) input) =
      initList (completedMachine headerPlan rowPlan) input := rfl

theorem finalTapes_eq (base : Tape → List Bool) :
    MachineDrainMany.finalTapes chosen base = MachineDrainMany.haltTapes .output (base .output) := by
  funext tape
  rw [MachineDrainMany.finalTapes_apply]
  simp only [mem_chosen]
  by_cases h : tape = .output
  · subst tape
    simp [MachineDrainMany.haltTapes]
  · simp [MachineDrainMany.haltTapes, h]

theorem haltList_eq (headerPlan rowPlan : Plan) (output : List Bool) :
    haltList (completedMachine headerPlan rowPlan) output =
      ⟨none, (FinalCNFMachine.Program.machine headerPlan rowPlan).initialState,
        MachineDrainMany.haltTapes .output output⟩ := by
  congr 1

/-- Actual drains followed by a real state-reset instruction reach canonical halt. -/
def cleanupExecution (headerPlan rowPlan : Plan) (state : State Unit) (base : Tape → List Bool) :
    StateTransition.EvalsToInTime (completedMachine headerPlan rowPlan).step
      ⟨cleanupEntry headerPlan rowPlan, state, base⟩
      (some (haltList (completedMachine headerPlan rowPlan) (base .output)))
      (MachineDrainMany.steps chosen base + 1) := by
  let after : (completedMachine headerPlan rowPlan).Cfg :=
    ⟨some (resetLabel headerPlan rowPlan),
      (state.1, MachineDrainMany.finalRegister chosen state.2),
      MachineDrainMany.finalTapes chosen base⟩
  have drains : StateTransition.EvalsToInTime (completedMachine headerPlan rowPlan).step
      ⟨cleanupEntry headerPlan rowPlan, state, base⟩ (some after)
      (MachineDrainMany.steps chosen base) := {
    steps := MachineDrainMany.steps chosen base
    evals_in_steps := MachineDrainMany.trace chosen (cleanupLabel headerPlan rowPlan)
      (some (resetLabel headerPlan rowPlan)) (completedProgram headerPlan rowPlan)
      (fun _ => rfl) base state.1 state.2
    steps_le_m := le_rfl }
  have reset : StateTransition.EvalsToInTime (completedMachine headerPlan rowPlan).step
      after (some (haltList (completedMachine headerPlan rowPlan) (base .output))) 1 := {
    steps := 1
    evals_in_steps := by
      change some (⟨none, (FinalCNFMachine.Program.machine headerPlan rowPlan).initialState,
        MachineDrainMany.finalTapes chosen base⟩ : (completedMachine headerPlan rowPlan).Cfg) =
          some (haltList (completedMachine headerPlan rowPlan) (base .output))
      erw [finalTapes_eq, haltList_eq]
      rfl
    steps_le_m := le_rfl }
  simpa only [Nat.add_comm] using
    StateTransition.EvalsToInTime.trans _ (MachineDrainMany.steps chosen base) 1
      _ after _ drains reset

/-- The extra cost is bounded from the actual raw execution, independently of
the contents of its dirty private tapes and finite state. -/
def outputsInTime (headerPlan rowPlan : Plan) (input output : List Bool)
    (state : State Unit) (base : Tape → List Bool) (budget : Nat)
    (raw : StateTransition.EvalsToInTime
      (FinalCNFMachine.Program.machine headerPlan rowPlan).step
      (initList (FinalCNFMachine.Program.machine headerPlan rowPlan) input)
      (some ⟨none, state, base⟩) budget)
    (correctOutput : base .output = output) :
    TM2OutputsInTime (completedMachine headerPlan rowPlan) input (some output)
      (budget + 12 * (input.length + budget *
        Runtime.programPushBound (FinalCNFMachine.Program.machine headerPlan rowPlan) + 1) + 1) := by
  let lifted := liftExecutionInTime
    (FinalCNFMachine.Program.machine headerPlan rowPlan).step
    (completedMachine headerPlan rowPlan).step (embeddedCfg headerPlan rowPlan)
    (step_simulation headerPlan rowPlan) raw
  have joined := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ lifted
    (cleanupExecution headerPlan rowPlan state base)
  have stackBound : ∀ tape, (base tape).length ≤ input.length + budget *
      Runtime.programPushBound (FinalCNFMachine.Program.machine headerPlan rowPlan) := by
    intro tape
    have h := Runtime.executionSizeBound
      (FinalCNFMachine.Program.machine headerPlan rowPlan).step
      (fun cfg => (cfg.stk tape).length)
      (Runtime.programPushBound (FinalCNFMachine.Program.machine headerPlan rowPlan))
      (Runtime.stepStackLength (FinalCNFMachine.Program.machine headerPlan rowPlan) tape) raw
    exact h.trans (Nat.add_le_add_right
      (Runtime.initialStackLength (FinalCNFMachine.Program.machine headerPlan rowPlan) input tape) _)
  have cleanupBound := MachineDrainMany.steps_le_uniform chosen base _ stackBound
  rw [chosen_length] at cleanupBound
  rw [embedded_init, correctOutput] at joined
  exact { toEvalsTo := joined.toEvalsTo
          steps_le_m := joined.steps_le_m.trans (by omega) }

/-- For fixed raw plans, polynomial raw time gives polynomial cleanup time. -/
noncomputable def completedTime (headerPlan rowPlan : Plan) (rawTime : Polynomial Nat) : Polynomial Nat :=
  rawTime + Polynomial.C 12 * (Polynomial.X + rawTime *
    Polynomial.C (Runtime.programPushBound (FinalCNFMachine.Program.machine headerPlan rowPlan)) + 1) + 1

theorem completedTime_eval (headerPlan rowPlan : Plan) (rawTime : Polynomial Nat) (n : Nat) :
    (completedTime headerPlan rowPlan rawTime).eval n =
      rawTime.eval n + 12 * (n + rawTime.eval n *
        Runtime.programPushBound (FinalCNFMachine.Program.machine headerPlan rowPlan) + 1) + 1 := by
  simp [completedTime]

end MaxCutGames.Foundations.Complexity.FinalCNFCleanup

/-!
The complete polynomial-time machine certificate for converting a validated
64-label graph table into its actual 3CNF formula. The proof composes the real
input parser, all row executions, output reversal, and private-tape cleanup.
-/

namespace MaxCutGames.Foundations.Complexity.FinalCNFMachine.Program

open Turing PCP

theorem emittedBytes_eq_formulaBits (table : GraphTables.Table) :
    emittedBytes rowPlan table = formulaBits (FinalTableFormula.output table) :=
  header_append_outputStream table

theorem rawBudget_le_phaseTime (table : GraphTables.Table) :
    rawBudget rowPlan table ≤ phaseTimePolynomial.eval (GraphTables.tableBits table).length := by
  unfold rawBudget
  rw [emittedBytes_eq_formulaBits]
  simpa only [Nat.add_assoc] using table_phaseTime_le table

/-- A concrete finite machine computes the complete CNF serialization from
the exact unary graph-table serialization, with a proved polynomial bound. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime GraphTables.tableBits formulaBits FinalTableFormula.output where
  tm := FinalCNFCleanup.completedMachine headerPlan rowPlan
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := finalTimePolynomial (Runtime.programPushBound (machine headerPlan rowPlan))
  outputsFun table := by
    change TM2OutputsInTime (FinalCNFCleanup.completedMachine headerPlan rowPlan)
      ((GraphTables.tableBits table).map id)
      (some ((formulaBits (FinalTableFormula.output table)).map id))
      ((finalTimePolynomial (Runtime.programPushBound (machine headerPlan rowPlan))).eval
        (GraphTables.tableBits table).length)
    have hi := @List.map_id
      ((FinalCNFCleanup.completedMachine headerPlan rowPlan).Γ
        (FinalCNFCleanup.completedMachine headerPlan rowPlan).k₀) (GraphTables.tableBits table)
    have ho := @List.map_id
      ((FinalCNFCleanup.completedMachine headerPlan rowPlan).Γ
        (FinalCNFCleanup.completedMachine headerPlan rowPlan).k₁)
      (formulaBits (FinalTableFormula.output table))
    rw [hi, ho, finalTimePolynomial_eval]
    let raw := rawRun rowPlan table
    let bounded : StateTransition.EvalsToInTime (machine headerPlan rowPlan).step
        (initList (machine headerPlan rowPlan) (GraphTables.tableBits table))
        (some ⟨none, ((raw.finalAmbient, ()), none), raw.finalTapes⟩)
        (phaseTimePolynomial.eval (GraphTables.tableBits table).length) := {
      toEvalsTo := raw.execution.toEvalsTo
      steps_le_m := raw.execution.steps_le_m.trans (rawBudget_le_phaseTime table) }
    have correct : raw.finalTapes .output = formulaBits (FinalTableFormula.output table) :=
      raw.output.trans (emittedBytes_eq_formulaBits table)
    have run := FinalCNFCleanup.outputsInTime headerPlan rowPlan
      (GraphTables.tableBits table) (formulaBits (FinalTableFormula.output table))
      ((raw.finalAmbient, ()), none) raw.finalTapes
      (phaseTimePolynomial.eval (GraphTables.tableBits table).length) bounded correct
    exact run

end MaxCutGames.Foundations.Complexity.FinalCNFMachine.Program

end OAI
