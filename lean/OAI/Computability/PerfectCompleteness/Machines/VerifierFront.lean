import OAI.Computability.PerfectCompleteness.Machines.ClockPreparation
import OAI.Computability.PerfectCompleteness.Machines.InputFrame
import OAI.Computability.UniqueGames.Machines.MachineCompositionLemmas
import OAI.Computability.UniqueGames.Machines.MachineCopy
import OAI.Computability.UniqueGames.Machines.MachineSubroutineLemmas
import OAI.Computability.UniqueGames.PCP.SourceMachine

namespace OAI

section

noncomputable section
namespace UniqueGamesTheorem.Foundations.Complexity.CookLevin.VerifierFront
open Turing MachineComposition
open UniqueGamesTheorem.Foundations.Hastad

abbrev Tape (V : NPVerifier) := Fin 3 ⊕ ClockPreparation.Layout (ClockPreparation.clockPolynomials V)
abbrev ExtraLabel (V : NPVerifier) := Fin 4 ⊕ ClockPreparation.ProgramLabel (ClockPreparation.clockPolynomials V)
abbrev Label (V : NPVerifier) := InputFrame.Label ⊕ ExtraLabel V
abbrev State (A : Type) := A × Option Bool
abbrev EmbeddedAlphabet (V : NPVerifier) := MachineEmbedding.Alphabet InputFrame.Alphabet
  (fun _ : ClockPreparation.Layout (ClockPreparation.clockPolynomials V) => Bool)

def raw (V : NPVerifier) : Tape V := .inl 0
def stream (V : NPVerifier) : Tape V := .inl 1
def scratch (V : NPVerifier) : Tape V := .inl 2
def clockSlots (V : NPVerifier) : ClockPreparation.Layout (ClockPreparation.clockPolynomials V) ↪ Tape V :=
  ⟨Sum.inr, Sum.inr_injective⟩
def lengthTape (V : NPVerifier) : Tape V := clockSlots V (.inl ())
def clockTape (V : NPVerifier) (c : ClockPreparation.Clock) : Tape V :=
  clockSlots V (ClockPreparation.outputSlot _ (ClockPreparation.clockOutput V c))
def phase (V : NPVerifier) (i : Fin 4) : Label V := .inr (.inl i)
def clockLabel (V : NPVerifier) (l : ClockPreparation.ProgramLabel (ClockPreparation.clockPolynomials V)) : Label V :=
  .inr (.inr l)

def frameStates (A : Type) : (InputFrame.State × A) ≃ State A where
  toFun s := (s.2, s.1.2)
  invFun s := (((), s.2), s.1)
  left_inv := by rintro ⟨⟨⟨⟩, r⟩, a⟩; rfl
  right_inv _ := rfl

def clockStates (A : Type) : MachineHorner.State A ≃ State A where
  toFun s := (s.1.1, s.2)
  invFun s := ((s.1, ()), s.2)
  left_inv := by rintro ⟨⟨a, ⟨⟩⟩, r⟩; rfl
  right_inv _ := rfl

theorem alphabet_eq (V : NPVerifier) : EmbeddedAlphabet V = (fun _ : Tape V => Bool) := by
  funext k
  cases k <;> rfl

variable {A : Type}

def extraProgram (V : NPVerifier) : ExtraLabel V → TM2.Stmt (fun _ : Tape V => Bool) (Label V) (State A)
  | .inl i => if i = 0 then
      Reduction.MachineTransfer.loopAt (raw V) (scratch V) id false (phase V 0) (some (phase V 1))
    else if i = 1 then
      MachineCopy.forkLoop (scratch V) (raw V) (stream V) false (phase V 1) (some (phase V 2))
    else if i = 2 then SourceMachine.fieldStart (lengthTape V) (phase V 3)
    else SourceMachine.fieldLoop (raw V) (lengthTape V) (phase V 3) (some (clockLabel V (.inl ())))
  | .inr l => MachineSubroutine.statement (clockLabel V) none
      (MachineStateEquiv.statement (clockStates A)
        (ClockPreparation.program (ClockPreparation.clockPolynomials V) (clockSlots V) l))

def innerExtra (V : NPVerifier) : ExtraLabel V →
    TM2.Stmt (EmbeddedAlphabet V) (Label V) (InputFrame.State × A) := fun l =>
  MachineStateEquiv.statement (frameStates A).symm
    (MachineAlphabetTransport.statement (alphabet_eq V).symm (extraProgram V l))

def embeddedProgram (V : NPVerifier) : Label V →
    TM2.Stmt (EmbeddedAlphabet V) (Label V) (InputFrame.State × A) :=
  MachineEmbedding.program (some (phase V 0)) InputFrame.program (innerExtra V)

def program (V : NPVerifier) : Label V → TM2.Stmt (fun _ : Tape V => Bool) (Label V) (State A) :=
  MachineAlphabetTransport.program (alphabet_eq V)
    (MachineStateEquiv.program (frameStates A) (embeddedProgram V))

@[simp] theorem program_extra (V : NPVerifier) (l : ExtraLabel V) :
    program (A := A) V (.inr l) = extraProgram V l := by
  simp only [program, MachineAlphabetTransport.program, MachineStateEquiv.program,
    embeddedProgram, MachineEmbedding.program, innerExtra]
  have h := MachineStateEquiv.statement_symm_statement (frameStates A).symm
    (MachineAlphabetTransport.statement (alphabet_eq V).symm (extraProgram (A := A) V l))
  simp only [Equiv.symm_symm] at h
  rw [h]
  exact MachineAlphabetTransport.statement_roundtrip _ _

def frameTapes (V : NPVerifier) (word : List Bool) : Tape V → List Bool
  | .inl i => if i = 0 then word else []
  | .inr _ => []

def framedTapes (V : NPVerifier) (input : List Bool) : Tape V → List Bool :=
  frameTapes V (encodeWord input.length ++ input)

def copiedTapes (V : NPVerifier) (input : List Bool) : Tape V → List Bool :=
  Function.update (framedTapes V input) (stream V) (encodeWord input.length ++ input)

def seedTapes (V : NPVerifier) (input : List Bool) : Tape V → List Bool :=
  Function.update (Function.update (copiedTapes V input) (raw V) input)
    (lengthTape V) (encodeWord input.length)

def preparedTapes (V : NPVerifier) (input : List Bool) : Tape V → List Bool :=
  ClockPreparation.resultTapes (ClockPreparation.clockPolynomials V) (clockSlots V)
    (seedTapes V input) input.length

private theorem alphabet_tapes_apply {K : Type} {Γ Δ : K → Type}
    (h : Γ = Δ) (base : ∀ k, List (Γ k)) (k : K) :
    MachineAlphabetTransport.tapes h base k =
      Eq.mp (congrArg (fun alphabet => List (alphabet k)) h) (base k) := by
  cases h
  rfl

theorem uniform_frame_tapes (V : NPVerifier) (word : List Bool) :
    MachineAlphabetTransport.tapes (alphabet_eq V)
      (MachineEmbedding.tapes (InputFrame.tapes word [] []) (fun _ => [])) = frameTapes V word := by
  funext k
  rw [alphabet_tapes_apply]
  cases k with
  | inl i => fin_cases i <;> rfl
  | inr k => rfl

def frameInTime (V : NPVerifier) (input : List Bool) (ambient : A) :
    StateTransition.EvalsToInTime (TM2.step (program V))
      ⟨some (.inl 0), (ambient, none), frameTapes V input⟩
      (some ⟨some (phase V 0), (ambient, none), framedTapes V input⟩)
      (4 * input.length + 7) := by
  have hi : initList InputFrame.machine input = InputFrame.cfg (some 0) input [] [] := by
    unfold initList InputFrame.cfg
    congr 1
    funext i
    fin_cases i <;> simp [InputFrame.machine, InputFrame.tapes]
  let original : StateTransition.EvalsToInTime (TM2.step InputFrame.program)
      (InputFrame.cfg (some 0) input [] [])
      (some (InputFrame.cfg none (encodeWord input.length ++ input) [] []))
      (4 * input.length + 7) := {
    steps := 4 * input.length + 7
    evals_in_steps := by
      rw [← hi, InputFrame.stopped_eq_haltList]
      exact InputFrame.frameTrace input
    steps_le_m := le_rfl }
  have em := embeddedExecution (some (phase V 0)) ambient (fun _ => [])
    InputFrame.program (innerExtra V) original
  have st := MachineStateEquiv.execution (frameStates A) (embeddedProgram V) em
  have result := MachineAlphabetTransport.executionInTime (alphabet_eq V)
    (MachineStateEquiv.program (frameStates A) (embeddedProgram V)) st
  simpa only [program, InputFrame.cfg, MachineAlphabetTransport.configuration_mk,
    MachineStateEquiv.configuration, MachineEmbedding.configuration, MachineEmbedding.label,
    Option.map_some, frameStates, Equiv.coe_fn_mk, uniform_frame_tapes, framedTapes] using result

def copyInTime (V : NPVerifier) (input : List Bool) (ambient : A) :
    StateTransition.EvalsToInTime (TM2.step (program V))
      ⟨some (phase V 0), (ambient, none), framedTapes V input⟩
      (some ⟨some (phase V 2), (ambient, none), copiedTapes V input⟩)
      (4 * input.length + 4) := by
  have run := MachineCopy.copyInTime (raw V) (stream V) (scratch V)
    (by simp [raw, stream]) (by simp [raw, scratch]) (by simp [stream, scratch])
    false (phase V 0) (phase V 1) (some (phase V 2)) (program V)
    (by simp [phase, extraProgram]) (by simp [phase, extraProgram])
    (framedTapes V input) (by simp [framedTapes, frameTapes, scratch]) ambient none
  have hb : 2 * ((framedTapes V input (raw V)).length + 1) = 4 * input.length + 4 := by
    simp only [framedTapes, frameTapes, raw, ite_true, List.length_append, encodeWord_length]
    omega
  rw [hb] at run
  simpa [framedTapes, frameTapes, raw, stream, copiedTapes] using run

def fieldInTime (V : NPVerifier) (input : List Bool) (ambient : A) :
    StateTransition.EvalsToInTime (TM2.step (program V))
      ⟨some (phase V 2), (ambient, none), copiedTapes V input⟩
      (some ⟨some (clockLabel V (.inl ())), (ambient, none), seedTapes V input⟩)
      (input.length + 2) := by
  have run := SourceMachine.fieldInTime (raw V) (lengthTape V)
    (by simp [raw, lengthTape, clockSlots]) (phase V 2) (phase V 3)
    (some (clockLabel V (.inl ()))) (program V)
    (by simp [phase, extraProgram]) (by simp [phase, extraProgram])
    (copiedTapes V input) input.length input
    (by simp [copiedTapes, raw, stream, framedTapes, frameTapes]) ambient none
  simpa [SourceMachine.fieldTapes, seedTapes, copiedTapes, lengthTape, clockSlots,
    stream, framedTapes, frameTapes] using run

theorem seed_input (V : NPVerifier) (input : List Bool) :
    seedTapes V input (clockSlots V (.inl ())) = encodeWord input.length := by
  simp [seedTapes, lengthTape]

theorem seed_clean (V : NPVerifier) (input : List Bool) :
    ClockPreparation.Clean (ClockPreparation.clockPolynomials V) (clockSlots V) (seedTapes V input) := by
  intro i
  simp [seedTapes, copiedTapes, framedTapes, frameTapes, lengthTape, raw, stream, clockSlots]

def clocksInTime (V : NPVerifier) (input : List Bool) (ambient : A) :
    StateTransition.EvalsToInTime (TM2.step (program V))
      ⟨some (clockLabel V (.inl ())), (ambient, none), seedTapes V input⟩
      (some ⟨none, (ambient, none), preparedTapes V input⟩)
      ((1 + ClockPreparation.timePolynomial (ClockPreparation.clockPolynomials V)).eval input.length) := by
  have original := ClockPreparation.clocksInTime V (clockSlots V) (seedTapes V input)
    input.length (seed_input V input) (seed_clean V input) ambient none
  have st := MachineStateEquiv.execution (clockStates A)
    (ClockPreparation.program (ClockPreparation.clockPolynomials V) (clockSlots V)) original
  have sub := MachineSubroutine.execution (clockLabel V) none
    (MachineStateEquiv.program (clockStates A)
      (ClockPreparation.program (ClockPreparation.clockPolynomials V) (clockSlots V)))
    (program V) (by intro l; simp [clockLabel, extraProgram, MachineStateEquiv.program]) st
  simpa only [MachineSubroutine.configuration, MachineSubroutine.label,
    MachineStateEquiv.configuration, Option.map_some, clockStates, Equiv.coe_fn_mk,
    preparedTapes] using sub

def timePolynomial (V : NPVerifier) : Polynomial Nat :=
  Polynomial.C 9 * Polynomial.X + Polynomial.C 14 + ClockPreparation.timePolynomial (ClockPreparation.clockPolynomials V)

def prepareInTime (V : NPVerifier) (input : List Bool) (ambient : A) :
    StateTransition.EvalsToInTime (TM2.step (program V))
      ⟨some (.inl 0), (ambient, none), frameTapes V input⟩
      (some ⟨none, (ambient, none), preparedTapes V input⟩)
      ((timePolynomial V).eval input.length) := by
  let one := frameInTime V input ambient
  let two := copyInTime V input ambient
  let three := fieldInTime V input ambient
  let four := clocksInTime V input ambient
  let a := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ one two
  let b := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ a three
  let c := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ b four
  exact {
    toEvalsTo := c.toEvalsTo
    steps_le_m := by
      have h := c.steps_le_m
      simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_X, Polynomial.eval_one] at *
      omega }

def callerInTime {Λ : Type} (V : NPVerifier) (labels : Label V → Λ) (exit : Option Λ)
    (caller : Λ → TM2.Stmt (fun _ : Tape V => Bool) Λ (State A))
    (atLabels : ∀ l, caller (labels l) = MachineSubroutine.statement labels exit (program V l))
    (input : List Bool) (ambient : A) :
    StateTransition.EvalsToInTime (TM2.step caller)
      ⟨some (labels (.inl 0)), (ambient, none), frameTapes V input⟩
      (some ⟨exit, (ambient, none), preparedTapes V input⟩)
      ((timePolynomial V).eval input.length) := by
  exact MachineSubroutine.execution labels exit (program V) caller atLabels
    (prepareInTime V input ambient)

theorem prepared_raw (V : NPVerifier) (input : List Bool) :
    preparedTapes V input (raw V) = input := by
  rw [preparedTapes, ClockPreparation.resultTapes_ambient]
  · simp [seedTapes, lengthTape, clockSlots, raw]
  · rintro ⟨i, hi⟩
    cases hi

theorem prepared_stream (V : NPVerifier) (input : List Bool) :
    preparedTapes V input (stream V) = encodeWord input.length ++ input := by
  rw [preparedTapes, ClockPreparation.resultTapes_ambient]
  · simp [seedTapes, lengthTape, clockSlots, raw, stream, copiedTapes]
  · rintro ⟨i, hi⟩
    cases hi

theorem prepared_length (V : NPVerifier) (input : List Bool) :
    preparedTapes V input (lengthTape V) = encodeWord input.length := by
  rw [preparedTapes, ClockPreparation.resultTapes_off_outputs]
  · exact seed_input V input
  · intro i h
    exact ClockPreparation.outputSlot_ne_input _ i ((clockSlots V).injective h)

theorem prepared_clock (V : NPVerifier) (input : List Bool) (c : ClockPreparation.Clock) :
    preparedTapes V input (clockTape V c) =
      encodeWord (ClockPreparation.clockValue V input.length c) :=
  ClockPreparation.clockResult_output V (clockSlots V) (seedTapes V input) input.length
    (seed_clean V input) c

theorem clockOutput_surjective (V : NPVerifier) :
    Function.Surjective (ClockPreparation.clockOutput V) := by
  intro i
  rcases i with (⟨⟩ | (⟨⟩ | (⟨⟩ | (⟨⟩ | (⟨⟩ | (⟨⟩ | i))))))
  · exact ⟨.witness, rfl⟩
  · exact ⟨.horizon, rfl⟩
  · exact ⟨.capacity, rfl⟩
  · exact ⟨.width, rfl⟩
  · exact ⟨.frameWidth, rfl⟩
  · exact ⟨.inputCount, rfl⟩
  · exact Empty.elim i

theorem prepared_work_clear (V : NPVerifier) (input : List Bool) (k : Tape V)
    (hr : k ≠ raw V) (hs : k ≠ stream V) (hn : k ≠ lengthTape V)
    (hc : ∀ c, k ≠ clockTape V c) : preparedTapes V input k = [] := by
  rw [preparedTapes, ClockPreparation.resultTapes_off_outputs]
  · simp only [seedTapes, Function.update_of_ne hn, Function.update_of_ne hr,
      copiedTapes, Function.update_of_ne hs, framedTapes]
    cases k with
    | inl i =>
      have hi : i ≠ 0 := by intro h; exact hr (congrArg Sum.inl h)
      simp [frameTapes, hi]
    | inr i => rfl
  · intro i h
    obtain ⟨c, rfl⟩ := clockOutput_surjective V i
    exact hc c h.symm

def machine (V : NPVerifier) : FinTM2 where
  K := Tape V
  k₀ := raw V
  k₁ := stream V
  Γ _ := Bool
  Λ := Label V
  main := .inl 0
  σ := State Unit
  initialState := ((), none)
  m := program V

theorem initial_configuration (V : NPVerifier) (input : List Bool) :
    initList (machine V) input =
      (⟨some (.inl 0), ((), none), frameTapes V input⟩ : (machine V).Cfg) := by
  unfold initList
  congr 1
  funext k
  cases k with
  | inl i =>
    by_cases hi : i = 0
    · simp [machine, raw, frameTapes, hi]
      rfl
    · simp [machine, raw, frameTapes, hi]
  | inr i => simp [machine, raw, frameTapes]

def machineInTime (V : NPVerifier) (input : List Bool) :
    StateTransition.EvalsToInTime (machine V).step (initList (machine V) input)
      (some ⟨none, ((), none), preparedTapes V input⟩)
      ((timePolynomial V).eval input.length) := by
  rw [initial_configuration]
  exact prepareInTime V input ()

theorem finite_work_alphabets (V : NPVerifier) (k : (machine V).K) :
    Finite ((machine V).Γ k) := by
  change Finite Bool
  infer_instance

end UniqueGamesTheorem.Foundations.Complexity.CookLevin.VerifierFront
end

end

end OAI
