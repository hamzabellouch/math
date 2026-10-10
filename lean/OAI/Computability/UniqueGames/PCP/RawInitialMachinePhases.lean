import OAI.Computability.UniqueGames.PCP.PreprocessingRegularLoopWordsLemmas

namespace OAI

/-! Actual execution of the raw initial graph program's reusable phases. -/

namespace UniqueGamesTheorem.Foundations.PCP.RawInitialMachinePhases

open Turing Complexity RawInitialMachineModel

theorem copySource_ne_scratch (phase : CopyPhase) : copySource phase ≠ Tape.scratch := by
  cases phase <;> simp [copySource]

theorem copySource_ne_reversed (phase : CopyPhase) : copySource phase ≠ Tape.reversed := by
  cases phase <;> simp [copySource]

def copyInTime (phase : CopyPhase) (base : Tape → List Bool)
    (n : Nat) (suffix : List Bool)
    (hsource : base (copySource phase) = encodeWord n ++ suffix)
    (hscratch : base .scratch = []) (state : State) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.scan phase), state, base⟩
      (some ⟨some (copyNext phase), (state.1, none),
        Function.update base .reversed
          (List.replicate (copyScale phase * n) true ++ base .reversed)⟩)
      (2 * n + 2) :=
  MachineInitialHeaders.prefixInTime (copySource phase) Tape.scratch Tape.reversed
    (copySource_ne_scratch phase) (copySource_ne_reversed phase) (by decide)
    (copyScale phase) (.scan phase) (.restore phase) (some (copyNext phase))
    program rfl rfl base n suffix hsource hscratch state.1 state.2

def relationInTime (slot : Fin 3) (orientation : Bool)
    (base : Tape → List Bool) (state : State) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.relation slot orientation), state, base⟩
      (some ⟨some (relationNext slot orientation), state,
        Function.update base .reversed
          (relationOutput slot orientation state ++ base .reversed)⟩) 1 :=
  MachineFiniteTable.emitInTime (K := Tape) (Λ := Label) (σ := State) (Γ := Alphabet)
    Tape.reversed
    (relationOutput slot orientation)
    stateKeys stateKeys_complete program (.relation slot orientation)
    (relationNext slot orientation) rfl state base

private theorem bitWord_head (b : Bool) :
    (encodeWord (if b then 1 else 0)).head? = some b := by
  cases b <;> rfl

theorem loadSigns_step (base : Tape → List Bool) (a b c : Bool)
    (ha : base (.field 1) = encodeWord (if a then 1 else 0))
    (hb : base (.field 3) = encodeWord (if b then 1 else 0))
    (hc : base (.field 5) = encodeWord (if c then 1 else 0)) (state : State) :
    (TM2.step program) ⟨some .loadSigns, state, base⟩ =
      some ⟨some (.scan (.tailVariables 0)), ((a, b, c), none), base⟩ := by
  change some (TM2.stepAux (program .loadSigns) state base) = _
  simp only [program, TM2.stepAux, ha, hb, hc, bitWord_head, Option.getD_some]

def loadSignsInTime (base : Tape → List Bool) (a b c : Bool)
    (ha : base (.field 1) = encodeWord (if a then 1 else 0))
    (hb : base (.field 3) = encodeWord (if b then 1 else 0))
    (hc : base (.field 5) = encodeWord (if c then 1 else 0)) (state : State) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some .loadSigns, state, base⟩
      (some ⟨some (.scan (.tailVariables 0)), ((a, b, c), none), base⟩) 1 where
  steps := 1
  evals_in_steps := loadSigns_step base a b c ha hb hc state
  steps_le_m := Nat.le_refl _

def cleanupFieldInTime (slot : Fin 6) (base : Tape → List Bool) (state : State) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.cleanupField slot), state, base⟩
      (some ⟨some (if h : slot.val + 1 < 6 then .cleanupField ⟨slot.val + 1, h⟩
        else .incrementIndex), (state.1, none), Function.update base (.field slot) []⟩)
      ((base (.field slot)).length + 1) :=
  MachineDrain.drainInTime (.field slot) (.cleanupField slot) _ program rfl base state.1 state.2

def cleanupFinalInTime (slot : Fin 3) (base : Tape → List Bool) (state : State) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.cleanupFinal slot), state, base⟩
      (some ⟨some (if h : slot.val + 1 < 3 then .cleanupFinal ⟨slot.val + 1, h⟩
        else .reset), (state.1, none), Function.update base (finalTape slot) []⟩)
      ((base (finalTape slot)).length + 1) :=
  MachineDrain.drainInTime (finalTape slot) (.cleanupFinal slot) _ program rfl base state.1 state.2

end UniqueGamesTheorem.Foundations.PCP.RawInitialMachinePhases

end OAI
