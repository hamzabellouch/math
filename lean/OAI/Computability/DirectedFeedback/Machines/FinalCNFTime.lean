import Mathlib
import OAI.Computability.DirectedFeedback.Machines.FinalCNFStream

namespace OAI

namespace DFVSGames.Foundations.Complexity.FinalCNFMachine.Program

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

theorem table_phaseTime_le (table : GraphTables.Table) :
    headerTimePolynomial.eval (GraphTables.tableBits table).length +
      (table.darts * (rowTime rowPlan (GraphTables.tableBits table).length + 1) + 1) +
      ((formulaBits (FinalTableFormula.output table)).length + 1) ≤
        phaseTimePolynomial.eval (GraphTables.tableBits table).length :=
  phaseTime_le (GraphTables.darts_le_tableBits_length table)
    (FinalTableFormula.formulaBits_length_le_polynomial table)

noncomputable def finalTimePolynomial (C : Nat) : Polynomial Nat :=
  phaseTimePolynomial + Polynomial.C 12 *
    (Polynomial.X + phaseTimePolynomial * Polynomial.C C + Polynomial.C 1) + Polynomial.C 1

theorem finalTimePolynomial_eval (C N : Nat) :
    (finalTimePolynomial C).eval N = phaseTimePolynomial.eval N +
      12 * (N + phaseTimePolynomial.eval N * C + 1) + 1 := by
  simp only [finalTimePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X]

theorem finalTime_le (C N workLength : Nat)
    (workBound : workLength ≤ N + phaseTimePolynomial.eval N * C) :
    phaseTimePolynomial.eval N + 12 * (workLength + 1) + 1 ≤
      (finalTimePolynomial C).eval N := by
  have h := Nat.mul_le_mul_left 12 (Nat.add_le_add_right workBound 1)
  rw [finalTimePolynomial_eval]
  omega

end DFVSGames.Foundations.Complexity.FinalCNFMachine.Program

namespace DFVSGames.Foundations.Complexity.FinalCNFCleanup

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
      exact congrArg some (stepAux_redirect Sum.inl (cleanupEntry headerPlan rowPlan)
        (FinalCNFMachine.Program.program headerPlan rowPlan label) state tapes)

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
      exact congrArg some ((congrArg
        (fun tapes : Tape → List Bool =>
          (⟨none, (FinalCNFMachine.Program.machine headerPlan rowPlan).initialState,
            tapes⟩ : (completedMachine headerPlan rowPlan).Cfg))
        (finalTapes_eq base)).trans (haltList_eq headerPlan rowPlan (base .output)).symm)
    steps_le_m := le_rfl }
  simpa only [Nat.add_comm] using
    StateTransition.EvalsToInTime.trans _ (MachineDrainMany.steps chosen base) 1
      _ after _ drains reset

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

noncomputable def completedTime (headerPlan rowPlan : Plan) (rawTime : Polynomial Nat) : Polynomial Nat :=
  rawTime + Polynomial.C 12 * (Polynomial.X + rawTime *
    Polynomial.C (Runtime.programPushBound (FinalCNFMachine.Program.machine headerPlan rowPlan)) + 1) + 1

theorem completedTime_eval (headerPlan rowPlan : Plan) (rawTime : Polynomial Nat) (n : Nat) :
    (completedTime headerPlan rowPlan rawTime).eval n =
      rawTime.eval n + 12 * (n + rawTime.eval n *
        Runtime.programPushBound (FinalCNFMachine.Program.machine headerPlan rowPlan) + 1) + 1 := by
  simp [completedTime]

end DFVSGames.Foundations.Complexity.FinalCNFCleanup

namespace DFVSGames.Foundations.Complexity.FinalCNFMachine.Program

open Turing PCP

theorem emittedBytes_eq_formulaBits (table : GraphTables.Table) :
    emittedBytes rowPlan table = formulaBits (FinalTableFormula.output table) :=
  header_append_outputStream table

theorem rawBudget_le_phaseTime (table : GraphTables.Table) :
    rawBudget rowPlan table ≤ phaseTimePolynomial.eval (GraphTables.tableBits table).length := by
  unfold rawBudget
  rw [emittedBytes_eq_formulaBits]
  simpa only [Nat.add_assoc] using table_phaseTime_le table

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
    have input_eq := @List.map_id
      ((FinalCNFCleanup.completedMachine headerPlan rowPlan).Γ
        (FinalCNFCleanup.completedMachine headerPlan rowPlan).k₀) (GraphTables.tableBits table)
    have output_eq := @List.map_id
      ((FinalCNFCleanup.completedMachine headerPlan rowPlan).Γ
        (FinalCNFCleanup.completedMachine headerPlan rowPlan).k₁)
      (formulaBits (FinalTableFormula.output table))
    rw [input_eq, output_eq, finalTimePolynomial_eval]
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

end DFVSGames.Foundations.Complexity.FinalCNFMachine.Program

namespace DFVSGames.Foundations.Complexity.MachineTableIteration

open Turing PCP RoundTables GraphIterationBounds

def finalTable (H : BaseTable) (input : Input) : GraphTables.Table :=
  TableIteration.runTables H (count input) input.val

noncomputable def counterCertificate : TM2ComputableInPolyTime inputBits countedBits (id : Input → Input) where
  toTM2ComputableAux := GraphCounterPrefix.computableInPolyTime.toTM2ComputableAux
  time := GraphCounterPrefix.computableInPolyTime.time
  outputsFun input := GraphCounterPrefix.computableInPolyTime.outputsFun input.val

variable (H : BaseTable)
  (body : TM2ComputableInPolyTime GraphTables.tableBits GraphTables.tableBits (build H))

private theorem countedBudget_le (input : Input) :
    count input + 1 + MachineRepeat.loopBudget (count input) (words H input)
      (fun index => body.time.eval (words H input index).length) ≤
        (runtimePolynomial body.time).eval (countedBits input).length := by
  let budgets := fun index => body.time.eval (words H input index).length
  let inputLength := (countedBits input).length
  let lengthBound := lengthPolynomial.eval inputLength
  let timeBound := body.time.eval lengthBound
  have length_le (index : Nat) (hindex : index ≤ count input) :
      (words H input index).length ≤ lengthBound :=
    intermediate_bits H input index hindex
  have budget_le (index : Nat) (hindex : index < count input) : budgets index ≤ timeBound :=
    MachineComposition.natPolynomial_eval_mono body.time (length_le index hindex.le)
  have loop_le := MachineRepeat.loopBudget_le (count input) (words H input) budgets
    timeBound lengthBound budget_le length_le
  have count_bound : count input ≤ inputLength + 1 := count_le input
  rw [runtimePolynomial_eval]
  calc
    count input + 1 + MachineRepeat.loopBudget (count input) (words H input) budgets
        ≤ count input + 1 +
          (count input * (timeBound + 2 * lengthBound + 3) + 2 * lengthBound + 3) :=
      Nat.add_le_add_left loop_le _
    _ = count input * (timeBound + 2 * lengthBound + 4) + 2 * lengthBound + 4 := by ring
    _ ≤ (inputLength + 1) * (timeBound + 2 * lengthBound + 4) + 2 * lengthBound + 4 :=
      Nat.add_le_add_right (Nat.add_le_add_right (Nat.mul_le_mul_right _ count_bound) _) _

private noncomputable def countedExecution (input : Input) :
    TM2OutputsInTime (MachineRepeat.machine body.tm body.inputAlphabet body.outputAlphabet)
      ((countedBits input).map body.inputAlphabet.symm)
      (some ((GraphTables.tableBits (finalTable H input)).map body.inputAlphabet.symm))
      (count input + 1 + MachineRepeat.loopBudget (count input) (words H input)
        (fun index => body.time.eval (words H input index).length)) := by
  let budgets := fun index => body.time.eval (words H input index).length
  have runs (index : Nat) (_hindex : index < count input) :
      TM2OutputsInTime body.tm ((words H input index).map body.inputAlphabet.symm)
        (some ((words H input (index + 1)).map body.outputAlphabet.symm)) (budgets index) := by
    exact body.outputsFun (TableIteration.runTables H index input.val)
  exact MachineRepeat.executeSequence body.tm body.inputAlphabet body.outputAlphabet
    (count input) (words H input) budgets runs

private def outputsInTime_mono {tm : FinTM2} {inputWord : List (tm.Γ tm.k₀)}
    {outputWord : Option (List (tm.Γ tm.k₁))} {budget bound : Nat}
    (run : TM2OutputsInTime tm inputWord outputWord budget) (budget_le : budget ≤ bound) :
    TM2OutputsInTime tm inputWord outputWord bound := {
  toEvalsTo := run.toEvalsTo
  steps_le_m := run.steps_le_m.trans budget_le
}

noncomputable def countedCertificate :
    TM2ComputableInPolyTime countedBits GraphTables.tableBits (finalTable H) where
  tm := MachineRepeat.machine body.tm body.inputAlphabet body.outputAlphabet
  inputAlphabet := body.inputAlphabet
  outputAlphabet := body.inputAlphabet
  time := runtimePolynomial body.time
  outputsFun input :=
    outputsInTime_mono (countedExecution H body input) (countedBudget_le H body input)

noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime inputBits GraphTables.tableBits (finalTable H) :=
  MachineSequential.composeBits counterCertificate (countedCertificate H body)

noncomputable def initialCertificate :
    TM2ComputableInPolyTime formulaBits inputBits initial where
  toTM2ComputableAux := MachineRawInitialTable.computableInPolyTime.toTM2ComputableAux
  time := MachineRawInitialTable.computableInPolyTime.time
  outputsFun F := MachineRawInitialTable.computableInPolyTime.outputsFun F

noncomputable def tableCertificate :
    TM2ComputableInPolyTime formulaBits GraphTables.tableBits (TableIteration.outputTable H) := by
  change TM2ComputableInPolyTime formulaBits GraphTables.tableBits
    (fun F => finalTable H (initial F))
  exact MachineSequential.composeBits (f := initial) (g := finalTable H)
    initialCertificate (computableInPolyTime H body)

noncomputable def gapMapCertificate :
    TM2ComputableInPolyTime formulaBits formulaBits (TableIteration.gapMap H) :=
  MachineSequential.composeBits (f := TableIteration.outputTable H) (g := FinalTableFormula.output)
    (tableCertificate H body)
    FinalCNFMachine.Program.computableInPolyTime

end DFVSGames.Foundations.Complexity.MachineTableIteration

namespace DFVSGames.Foundations.Complexity.TableIterationFiniteAlphabet

open PCP MachineFiniteAlphabet

theorem initial : FiniteAlphabet MachineRawInitialTable.computableInPolyTime.tm := by
  intro k
  change Finite Bool
  infer_instance

theorem finalCNF : FiniteAlphabet FinalCNFMachine.Program.computableInPolyTime.tm := by
  intro k
  change Finite Bool
  infer_instance

theorem counter : FiniteAlphabet MachineTableIteration.counterCertificate.tm := by
  intro k
  change Finite Bool
  infer_instance

variable (H : RoundTables.BaseTable)
  (body : Turing.TM2ComputableInPolyTime GraphTables.tableBits GraphTables.tableBits
    (RoundTables.build H))
  (finiteBody : FiniteAlphabet body.tm)

include finiteBody

theorem counted : FiniteAlphabet (MachineTableIteration.countedCertificate H body).tm :=
  repeat_machine body.tm body.inputAlphabet body.outputAlphabet finiteBody

theorem iteration : FiniteAlphabet (MachineTableIteration.computableInPolyTime H body).tm :=
  composeBits MachineTableIteration.counterCertificate
    (MachineTableIteration.countedCertificate H body) counter (counted H body finiteBody)

theorem table : FiniteAlphabet (MachineTableIteration.tableCertificate H body).tm :=
  composeBits MachineTableIteration.initialCertificate
    (MachineTableIteration.computableInPolyTime H body) initial (iteration H body finiteBody)

theorem gapMap : FiniteAlphabet (MachineTableIteration.gapMapCertificate H body).tm :=
  composeBits (MachineTableIteration.tableCertificate H body)
    FinalCNFMachine.Program.computableInPolyTime (table H body finiteBody) finalCNF

end DFVSGames.Foundations.Complexity.TableIterationFiniteAlphabet

namespace DFVSGames.Reduction.Incidence

universe u v

structure Triple where
  first : Bool
  second : Bool
  third : Bool
  deriving DecidableEq

def parity (a : Triple) : Bool := (a.first.xor a.second).xor a.third

def matchingSlots (a b : Triple) : Nat :=
  (if a.first = b.first then 1 else 0) +
  (if a.second = b.second then 1 else 0) +
  (if a.third = b.third then 1 else 0)

def acceptedSlots (a b : Triple) (rhs : Bool) : Nat :=
  if parity a = rhs then matchingSlots a b else 0

def failedEquation (b : Triple) (rhs : Bool) : Nat :=
  if parity b = rhs then 0 else 1

def bestResponse (b : Triple) (rhs : Bool) : Triple :=
  if parity b = rhs then b else { b with first := !b.first }

theorem local_count_bound (a b : Triple) (rhs : Bool) :
    acceptedSlots a b rhs + failedEquation b rhs ≤ 3 := by
  rcases a with ⟨a₁, a₂, a₃⟩
  rcases b with ⟨b₁, b₂, b₃⟩
  cases a₁ <;> cases a₂ <;> cases a₃ <;>
    cases b₁ <;> cases b₂ <;> cases b₃ <;> cases rhs <;> decide

theorem best_response_exact (b : Triple) (rhs : Bool) :
    acceptedSlots (bestResponse b rhs) b rhs + failedEquation b rhs = 3 := by
  rcases b with ⟨b₁, b₂, b₃⟩
  cases b₁ <;> cases b₂ <;> cases b₃ <;> cases rhs <;> decide

structure Equation (Variable : Type u) where
  first : Variable
  second : Variable
  third : Variable
  rhs : Bool

variable {Variable : Type u} {Index : Type v}

inductive Slot where
  | first
  | second
  | third
  deriving DecidableEq

def nameAt (e : Equation Variable) : Slot → Variable
  | .first => e.first
  | .second => e.second
  | .third => e.third

def bitAt (a : Triple) : Slot → Bool
  | .first => a.first
  | .second => a.second
  | .third => a.third

def questionPredicate (e : Equation Variable) (name : Variable)
    (alice : Triple) (bob : Bool) : Prop :=
  parity alice = e.rhs ∧
    ((e.first = name ∧ alice.first = bob) ∨
     (e.second = name ∧ alice.second = bob) ∨
     (e.third = name ∧ alice.third = bob))

theorem question_predicate_at_slot (e : Equation Variable)
    (distinct₁₂ : e.first ≠ e.second) (distinct₁₃ : e.first ≠ e.third)
    (distinct₂₃ : e.second ≠ e.third) (alice : Triple) (bob : Bool) (slot : Slot) :
    questionPredicate e (nameAt e slot) alice bob ↔
      parity alice = e.rhs ∧ bitAt alice slot = bob := by
  cases slot <;>
    simp [questionPredicate, nameAt, bitAt, distinct₁₂, distinct₁₃, distinct₂₃,
      Ne.symm distinct₁₂, Ne.symm distinct₁₃, Ne.symm distinct₂₃]

def bobTriple (g : Variable → Bool) (e : Equation Variable) : Triple :=
  ⟨g e.first, g e.second, g e.third⟩

def acceptedCount (equations : Index → Equation Variable)
    (g : Variable → Bool) (alice : Index → Triple) : List Index → Nat
  | [] => 0
  | i :: rest =>
    acceptedSlots (alice i) (bobTriple g (equations i)) (equations i).rhs +
      acceptedCount equations g alice rest

def failureCount (equations : Index → Equation Variable)
    (g : Variable → Bool) : List Index → Nat
  | [] => 0
  | i :: rest =>
    failedEquation (bobTriple g (equations i)) (equations i).rhs +
      failureCount equations g rest

theorem total_count_bound (equations : Index → Equation Variable)
    (g : Variable → Bool) (alice : Index → Triple) (occurrences : List Index) :
    acceptedCount equations g alice occurrences + failureCount equations g occurrences ≤
      3 * occurrences.length := by
  induction occurrences with
  | nil => simp [acceptedCount, failureCount]
  | cons i rest ih =>
    have h := local_count_bound (alice i) (bobTriple g (equations i)) (equations i).rhs
    simp only [acceptedCount, failureCount, List.length_cons]
    omega

def optimalAlice (equations : Index → Equation Variable) (g : Variable → Bool)
    (i : Index) : Triple :=
  bestResponse (bobTriple g (equations i)) (equations i).rhs

theorem optimal_alice_exact (equations : Index → Equation Variable)
    (g : Variable → Bool) (occurrences : List Index) :
    acceptedCount equations g (optimalAlice equations g) occurrences +
      failureCount equations g occurrences = 3 * occurrences.length := by
  induction occurrences with
  | nil => simp [acceptedCount, failureCount]
  | cons i rest ih =>
    have h := best_response_exact (bobTriple g (equations i)) (equations i).rhs
    simp only [acceptedCount, failureCount, List.length_cons, optimalAlice]
    omega

theorem fixed_bob_optimum (equations : Index → Equation Variable)
    (g : Variable → Bool) (occurrences : List Index) :
    ∃ alice : Index → Triple,
      acceptedCount equations g alice occurrences + failureCount equations g occurrences =
        3 * occurrences.length ∧
      ∀ other : Index → Triple,
        acceptedCount equations g other occurrences ≤
          acceptedCount equations g alice occurrences := by
  refine ⟨optimalAlice equations g, optimal_alice_exact equations g occurrences, ?_⟩
  intro other
  have h := total_count_bound equations g other occurrences
  have heq := optimal_alice_exact equations g occurrences
  omega

theorem soundness_191_over_192 (equations : Index → Equation Variable)
    (g : Variable → Bool) (alice : Index → Triple) (occurrences : List Index)
    (source_gap : occurrences.length ≤ 64 * failureCount equations g occurrences) :
    64 * acceptedCount equations g alice occurrences ≤ 191 * occurrences.length := by
  have h := total_count_bound equations g alice occurrences
  omega

theorem game_soundness_191_over_192 (equations : Index → Equation Variable)
    (occurrences : List Index)
    (source_gap : ∀ g : Variable → Bool,
      occurrences.length ≤ 64 * failureCount equations g occurrences) :
    ∀ (g : Variable → Bool) (alice : Index → Triple),
      64 * acceptedCount equations g alice occurrences ≤ 191 * occurrences.length := by
  intro g alice
  exact soundness_191_over_192 equations g alice occurrences (source_gap g)

end DFVSGames.Reduction.Incidence

namespace DFVSGames.Reduction.SourceIncidence

variable {Name : Type} {Index : Type*}

def toIncidence (e : CloneGap.Equation Name) : Incidence.Equation Name :=
  ⟨e.first, e.second, e.third, e.rhs⟩

theorem failedEquation_eq (e : CloneGap.Equation Name) (g : Name → Bool) :
    Incidence.failedEquation (Incidence.bobTriple g (toIncidence e)) (toIncidence e).rhs =
      if CloneGap.satisfied e g then 0 else 1 := by
  simp only [Incidence.failedEquation, Incidence.bobTriple, toIncidence,
    Incidence.parity, CloneGap.satisfied]
  simp

theorem failureCount_eq (equations : Index → CloneGap.Equation Name)
    (g : Name → Bool) (occurrences : List Index) :
    Incidence.failureCount (fun i => toIncidence (equations i)) g occurrences =
      occurrences.countP (fun i => !CloneGap.satisfied (equations i) g) := by
  induction occurrences with
  | nil => rfl
  | cons i rest ih =>
    simp only [Incidence.failureCount, failedEquation_eq, ih, List.countP_cons]
    cases CloneGap.satisfied (equations i) g <;> simp ; omega

def occurrenceList (source : List (CloneGap.Equation Name)) :=
  (CloneGap.cloneList source).zipIdx

theorem cloned_occurrence_gap (source : List (CloneGap.Equation Name))
    (source_gap : ∀ A : Name → Bool,
      source.length ≤ 4 * source.countP (fun e => !CloneGap.satisfied e A))
    (g : Name × CloneGap.Index → Bool) :
    (occurrenceList source).length ≤ 64 *
      Incidence.failureCount (fun i => toIncidence i.1) g (occurrenceList source) := by
  have hg := CloneGap.clone_gap source source_gap g
  rw [failureCount_eq]
  unfold occurrenceList
  rw [List.length_zipIdx]
  have hcount : ((CloneGap.cloneList source).zipIdx).countP
      (fun i => !CloneGap.satisfied i.1 g) =
      (CloneGap.cloneList source).countP (fun e => !CloneGap.satisfied e g) := by
    have h := congrArg (fun es => es.countP (fun e => !CloneGap.satisfied e g))
      (List.zipIdx_map_fst 0 (CloneGap.cloneList source))
    simpa only [List.countP_map, Function.comp_def] using h
  rw [hcount]
  exact hg

theorem source_to_incidence_soundness (source : List (CloneGap.Equation Name))
    (source_gap : ∀ A : Name → Bool,
      source.length ≤ 4 * source.countP (fun e => !CloneGap.satisfied e A))
    (g : Name × CloneGap.Index → Bool)
    (alice : CloneGap.Equation (Name × CloneGap.Index) × Nat → Incidence.Triple) :
    64 * Incidence.acceptedCount (fun i => toIncidence i.1) g alice
      (occurrenceList source) ≤ 191 * (occurrenceList source).length := by
  exact Incidence.soundness_191_over_192 _ g alice _
    (cloned_occurrence_gap source source_gap g)

end DFVSGames.Reduction.SourceIncidence

end OAI
