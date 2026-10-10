import Mathlib
import OAI.Computability.DirectedFeedback.Machines.MachineExpanderRowDivision

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Foundations.Complexity.MachineExpanderFamily

open Turing

def boolWord : (tape : Tape) → List Bool → List (Alphabet tape)
  | .inl (.inl _), word => word
  | .inl (.inr _), word => word
  | .inr _, word => word

def toBoolWord : (tape : Tape) → List (Alphabet tape) → List Bool
  | .inl (.inl _), word => word
  | .inl (.inr _), word => word
  | .inr _, word => word

def fromBoolTapes (base : Tape → List Bool) : (tape : Tape) → List (Alphabet tape) :=
  fun tape => boolWord tape (base tape)

def toBoolTapes (base : (tape : Tape) → List (Alphabet tape)) : Tape → List Bool :=
  fun tape => toBoolWord tape (base tape)

@[simp] theorem toBoolWord_boolWord (tape : Tape) (word : List Bool) :
    toBoolWord tape (boolWord tape word) = word := by
  rcases tape with tape | tape
  · cases tape <;> rfl
  · rfl

@[simp] theorem boolWord_toBoolWord (tape : Tape) (word : List (Alphabet tape)) :
    boolWord tape (toBoolWord tape word) = word := by
  rcases tape with tape | tape
  · cases tape <;> rfl
  · rfl

@[simp] theorem toBool_fromBool (base : Tape → List Bool) :
    toBoolTapes (fromBoolTapes base) = base := by
  funext tape
  exact toBoolWord_boolWord tape (base tape)

@[simp] theorem fromBool_toBool (base : (tape : Tape) → List (Alphabet tape)) :
    fromBoolTapes (toBoolTapes base) = base := by
  funext tape
  exact boolWord_toBoolWord tape (base tape)

private theorem transport_tapes_apply_inline_MachineExpanderFamilyTapes {K : Type} {Γ Δ : K → Type}
    (h : Γ = Δ) (base : (k : K) → List (Γ k)) (k : K) :
    MachineAlphabetTransport.tapes h base k =
      Eq.mp (congrArg (fun alphabet => List (alphabet k)) h) (base k) := by
  cases h
  rfl

theorem toBoolTapes_eq_transport (base : (tape : Tape) → List (Alphabet tape)) :
    toBoolTapes base = MachineAlphabetTransport.tapes alphabet_eq base := by
  funext tape
  rw [transport_tapes_apply_inline_MachineExpanderFamilyTapes]
  rcases tape with tape | tape
  · cases tape <;> rfl
  · rfl

theorem fromBoolTapes_eq_transport (base : Tape → List Bool) :
    fromBoolTapes base = MachineAlphabetTransport.tapes alphabet_eq.symm base := by
  funext tape
  rw [transport_tapes_apply_inline_MachineExpanderFamilyTapes]
  rcases tape with tape | tape
  · cases tape <;> rfl
  · rfl

@[simp] theorem fromBoolTapes_update (base : Tape → List Bool) (tape : Tape) (word : List Bool) :
    fromBoolTapes (Function.update base tape word) =
      Function.update (fromBoolTapes base) tape (boolWord tape word) := by
  funext k
  by_cases h : k = tape
  · subst k
    simp [fromBoolTapes]
  · simp [fromBoolTapes, h]

@[simp] theorem toBoolTapes_update (base : (tape : Tape) → List (Alphabet tape))
    (tape : Tape) (word : List (Alphabet tape)) :
    toBoolTapes (Function.update base tape word) =
      Function.update (toBoolTapes base) tape (toBoolWord tape word) := by
  funext k
  by_cases h : k = tape
  · subst k
    simp [toBoolTapes]
  · simp [toBoolTapes, h]

theorem configuration_fromBool {ρ : Type} {d : Nat} (label : Option (Label d))
    (state : State ρ d) (base : Tape → List Bool) :
    MachineAlphabetTransport.configuration alphabet_eq.symm ⟨label, state, base⟩ =
      ⟨label, state, fromBoolTapes base⟩ := by
  rw [MachineAlphabetTransport.configuration_mk, fromBoolTapes_eq_transport]

theorem configuration_toBool {ρ : Type} {d : Nat} (label : Option (Label d))
    (state : State ρ d) (base : (tape : Tape) → List (Alphabet tape)) :
    MachineAlphabetTransport.configuration alphabet_eq ⟨label, state, base⟩ =
      ⟨label, state, toBoolTapes base⟩ := by
  rw [MachineAlphabetTransport.configuration_mk, toBoolTapes_eq_transport]

end DFVSGames.Foundations.Complexity.MachineExpanderFamily
end

section

namespace DFVSGames.Foundations.Complexity.MachineExpanderFamily

open Turing MachineComposition
open PCP.ExpanderTables PCP.ExpanderRowControl

theorem controlStatementInverse {K Λ σ τ : Type} {Γ : K → Type}
    (states : σ ≃ τ) (q : TM2.Stmt Γ Λ σ) :
    MachineControl.statement id states.symm (MachineControl.statement id states q) = q := by
  induction q <;>
    simp_all only [MachineControl.statement, Equiv.apply_symm_apply,
      Equiv.symm_apply_apply, id_eq]

theorem controlTrace {K Λ σ τ : Type} {Γ : K → Type} [DecidableEq K]
    (states : σ ≃ τ) (target : Λ → TM2.Stmt Γ Λ τ)
    (n : Nat) (start finish : TM2.Cfg Γ Λ σ)
    (run : (advance (TM2.step (MachineControl.program (Equiv.refl Λ) states.symm target)))^[n]
      (some start) = some finish) :
    (advance (TM2.step target))^[n]
      (some (MachineControl.configuration id states start)) =
      some (MachineControl.configuration id states finish) := by
  let source := MachineControl.program (Equiv.refl Λ) states.symm target
  have roundtrip : MachineControl.program (Equiv.refl Λ) states source = target := by
    funext label
    change MachineControl.statement id states
      (MachineControl.statement id states.symm (target label)) = target label
    exact controlStatementInverse states.symm _
  have simulation : ∀ a b, TM2.step source a = some b →
      TM2.step target (MachineControl.configuration id states a) =
        some (MachineControl.configuration id states b) := by
    intro a b hab
    have h := MachineControl.step_simulation (Equiv.refl Λ) states source a
    rw [roundtrip, hab] at h
    exact h
  exact liftSuccessfulTrace (TM2.step source) (TM2.step target)
    (MachineControl.configuration id states) simulation n start finish run

theorem controlDrainTrace {K Λ σ τ : Type} [DecidableEq K]
    (states : (σ × Option Bool) ≃ τ) (source : K) (again : Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ τ)
    (code : target again = MachineControl.statement id states
      (MachineDrain.drain source again exit))
    (base : K → List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step target))^[(base source).length + 1]
      (some ⟨some again, states (ambient, register), base⟩) =
      some ⟨exit, states (ambient, none), Function.update base source []⟩ := by
  let raw := MachineControl.program (Equiv.refl Λ) states.symm target
  have atRaw : raw again = MachineDrain.drain source again exit := by
    change MachineControl.statement id states.symm (target again) = _
    rw [code]
    exact controlStatementInverse states _
  have run := MachineDrain.drainTrace source again exit raw atRaw base (base source) ambient register
  simp only [Function.update_eq_self] at run
  simpa only [MachineControl.configuration, Option.map_some, id_eq, Option.map_id] using
    controlTrace states target ((base source).length + 1) _ _ run

theorem controlTransferTrace {K Λ σ τ : Type} [DecidableEq K]
    (states : (σ × Option Bool) ≃ τ) (source destination : K)
    (distinct : source ≠ destination) (again : Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ τ)
    (code : target again = MachineControl.statement id states
      (Reduction.MachineTransfer.loopAt source destination id false again exit))
    (base : K → List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step target))^[(base source).length + 1]
      (some ⟨some again, states (ambient, register), base⟩) =
      some ⟨exit, states (ambient, none),
        Reduction.MachineTransfer.tapesAt source destination base []
          ((base source).reverse ++ base destination)⟩ := by
  let raw := MachineControl.program (Equiv.refl Λ) states.symm target
  have atRaw : raw again = Reduction.MachineTransfer.loopAt source destination id false again exit := by
    change MachineControl.statement id states.symm (target again) = _
    rw [code]
    exact controlStatementInverse states _
  have run := Reduction.MachineTransfer.transferAt_fromTapes source destination distinct id false
    again exit raw atRaw base ambient register
  unfold Reduction.MachineTransfer.nextAt at run
  simpa only [MachineControl.configuration, Option.map_some, id_eq, Option.map_id,
    List.map_id] using controlTrace states target ((base source).length + 1) _ _ run

variable {ρ : Type} {d : Nat}

def clearRegister (state : State ρ d) : State ρ d :=
  (MachineExpanderTable.clearRegister state.1, state.2)

@[simp] theorem registerStates_reset (state : State ρ d) :
    registerStates ρ d (((registerStates ρ d).symm state).1, none) =
      clearRegister state := rfl

@[simp] theorem clearRegister_idempotent (state : State ρ d) :
    clearRegister (clearRegister state) = clearRegister state := rfl

@[simp] theorem caller_clearRegister (state : State ρ d) :
    caller (clearRegister state) = caller state := rfl

@[simp] theorem clearRegister_position (state : State ρ d) :
    (clearRegister state).1.2 = state.1.2 := rfl

@[simp] theorem clearRegister_register (state : State ρ d) :
    (clearRegister state).1.1.2 = none := rfl

variable [Fintype ρ]

theorem boolTraceActual (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (n : Nat)
    (start finish : TM2.Cfg BoolAlphabet (Label d) (State ρ d))
    (run : (advance (TM2.step (boolView positive H growth)))^[n] (some start) = some finish) :
    (advance (TM2.step (program positive H growth)))^[n]
      (some (MachineAlphabetTransport.configuration alphabet_eq.symm start)) =
      some (MachineAlphabetTransport.configuration alphabet_eq.symm finish) := by
  have h := MachineAlphabetTransport.successfulTrace alphabet_eq.symm
    (boolView positive H growth) n start finish run
  simpa only [boolView, MachineAlphabetTransport.program_symm_roundtrip] using h

theorem drainBoolTrace (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (source : Tape) (again next : OuterLabel)
    (code : boolOuterStatement (ρ := ρ) positive H again = drainStatement source again next)
    (base : Tape → List Bool) (state : State ρ d) :
    (advance (TM2.step (boolView positive H growth)))^[(base source).length + 1]
      (some ⟨some (.inr again), state, base⟩) =
      some ⟨some (.inr next), clearRegister state, Function.update base source []⟩ := by
  have atLoop : boolView (ρ := ρ) positive H growth (.inr again) =
      MachineControl.statement id (registerStates ρ d)
        (MachineDrain.drain source (.inr again) (some (.inr next))) := by
    rw [boolView_outer, code]
    rfl
  have h := controlDrainTrace (registerStates ρ d) source (.inr again) (some (.inr next))
    (boolView positive H growth) atLoop base
    ((registerStates ρ d).symm state).1 ((registerStates ρ d).symm state).2
  simpa only [Prod.mk.eta, Equiv.apply_symm_apply, registerStates_reset] using h

theorem transferBoolTrace (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (source destination : Tape) (distinct : source ≠ destination)
    (again next : OuterLabel)
    (code : boolOuterStatement (ρ := ρ) positive H again =
      MachineControl.statement id (registerStates ρ d)
        (Reduction.MachineTransfer.loopAt (Γ := BoolAlphabet) source destination id false
          (.inr again) (some (.inr next))))
    (base : Tape → List Bool) (state : State ρ d) :
    (advance (TM2.step (boolView positive H growth)))^[(base source).length + 1]
      (some ⟨some (.inr again), state, base⟩) =
      some ⟨some (.inr next), clearRegister state,
        Reduction.MachineTransfer.tapesAt source destination base []
          ((base source).reverse ++ base destination)⟩ := by
  have atLoop : boolView (ρ := ρ) positive H growth (.inr again) =
      MachineControl.statement id (registerStates ρ d)
        (Reduction.MachineTransfer.loopAt source destination id false
          (.inr again) (some (.inr next))) := by
    rw [boolView_outer, code]
  have h := controlTransferTrace (registerStates ρ d) source destination distinct
    (.inr again) (some (.inr next)) (boolView positive H growth) atLoop base
    ((registerStates ρ d).symm state).1 ((registerStates ρ d).symm state).2
  simpa only [Prod.mk.eta, Equiv.apply_symm_apply, registerStates_reset] using h

def installedTapes (base : Tape → List Bool) (newWord : List Bool) : Tape → List Bool :=
  Function.update
    (Function.update
      (Function.update (Function.update base tableTape newWord) resultTape [])
      (.inr .tableReverse) [])
    (.inr .currentSize) []

def cleanedCounterTapes (base : Tape → List Bool) : Tape → List Bool :=
  Function.update (Function.update base inputVertexTape []) vertexCountTape []

theorem installTableBoolTrace (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (base : Tape → List Bool) (newWord : List Bool)
    (resultWord : base resultTape = newWord) (reverseEmpty : base (.inr .tableReverse) = [])
    (state : State ρ d) :
    (advance (TM2.step (boolView positive H growth)))^[
        (base tableTape).length + 2 * newWord.length + (base (.inr .currentSize)).length + 4]
      (some ⟨some (.inr .clearOldTable), state, base⟩) =
      some ⟨some (.inr (.affine .multiplySize .seed)), clearRegister state,
        installedTapes base newWord⟩ := by
  let b0 := Function.update base tableTape []
  let b1 := Function.update (Function.update b0 resultTape []) (.inr .tableReverse) newWord.reverse
  let b2 := Function.update (Function.update b1 (.inr .tableReverse) []) tableTape newWord
  let b3 := Function.update b2 (.inr .currentSize) []
  have h0 := drainBoolTrace positive H growth tableTape .clearOldTable .reverseResult rfl base state
  have b0Result : b0 resultTape = newWord := by
    simpa [b0, tableTape, resultTape] using resultWord
  have b0Reverse : b0 (.inr .tableReverse) = [] := by
    simpa [b0, tableTape] using reverseEmpty
  have h1 : (advance (TM2.step (boolView positive H growth)))^[newWord.length + 1]
      (some ⟨some (.inr .reverseResult), clearRegister state, b0⟩) =
      some ⟨some (.inr .reverseTable), clearRegister state, b1⟩ := by
    simpa only [b0Result, b0Reverse, List.append_nil, Reduction.MachineTransfer.tapesAt,
      clearRegister_idempotent] using
      transferBoolTrace positive H growth resultTape (.inr .tableReverse) (by decide)
        .reverseResult .reverseTable rfl b0 (clearRegister state)
  have b1Reverse : b1 (.inr .tableReverse) = newWord.reverse := by simp [b1]
  have b1Table : b1 tableTape = [] := by simp [b1, b0, tableTape, resultTape]
  have h2 : (advance (TM2.step (boolView positive H growth)))^[newWord.length + 1]
      (some ⟨some (.inr .reverseTable), clearRegister state, b1⟩) =
      some ⟨some (.inr .clearCurrentSize), clearRegister state, b2⟩ := by
    simpa only [b1Reverse, b1Table, List.reverse_reverse, List.length_reverse,
      List.append_nil, Reduction.MachineTransfer.tapesAt, clearRegister_idempotent] using
      transferBoolTrace positive H growth (.inr .tableReverse) tableTape (by decide)
        .reverseTable .clearCurrentSize rfl b1 (clearRegister state)
  have b2Current : b2 (.inr .currentSize) = base (.inr .currentSize) := by
    simp [b2, b1, b0, tableTape, resultTape]
  have h3 : (advance (TM2.step (boolView positive H growth)))^[
      (base (.inr .currentSize)).length + 1]
      (some ⟨some (.inr .clearCurrentSize), clearRegister state, b2⟩) =
      some ⟨some (.inr (.affine .multiplySize .seed)), clearRegister state, b3⟩ := by
    simpa only [b2Current, clearRegister_idempotent] using
      drainBoolTrace positive H growth (.inr .currentSize) .clearCurrentSize
        (.affine .multiplySize .seed) rfl b2 (clearRegister state)
  have final : b3 = installedTapes base newWord := by
    funext tape
    rcases tape with table | extra
    · rcases table with row | tableExtra
      · cases row <;> simp [b3, b2, b1, b0, installedTapes, tableTape, resultTape]
      · cases tableExtra <;> simp [b3, b2, b1, b0, installedTapes, tableTape, resultTape]
    · cases extra <;> simp [b3, b2, b1, b0, installedTapes, tableTape, resultTape]
  rw [show (base tableTape).length + 2 * newWord.length +
        (base (.inr .currentSize)).length + 4 =
      ((base (.inr .currentSize)).length + 1) +
        ((newWord.length + 1) + ((newWord.length + 1) + ((base tableTape).length + 1))) by omega,
    Function.iterate_add_apply _ ((base (.inr .currentSize)).length + 1),
    Function.iterate_add_apply _ (newWord.length + 1) ((newWord.length + 1) + ((base tableTape).length + 1)),
    Function.iterate_add_apply _ (newWord.length + 1) ((base tableTape).length + 1),
    h0, h1, h2, h3, final]

theorem cleanupCountersBoolTrace (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (base : Tape → List Bool) (state : State ρ d) :
    (advance (TM2.step (boolView positive H growth)))^[
        (base inputVertexTape).length + (base vertexCountTape).length + 2]
      (some ⟨some (.inr .drainInputVertex), state, base⟩) =
      some ⟨some (.inr .levelGuard), clearRegister state, cleanedCounterTapes base⟩ := by
  have h0 := drainBoolTrace positive H growth inputVertexTape .drainInputVertex .drainVertexCount
    rfl base state
  have count : (Function.update base inputVertexTape []) vertexCountTape = base vertexCountTape := by
    simp [inputVertexTape, vertexCountTape]
  have h1 := drainBoolTrace positive H growth vertexCountTape .drainVertexCount .levelGuard
    rfl (Function.update base inputVertexTape []) (clearRegister state)
  simp only [count, clearRegister_idempotent] at h1
  rw [show (base inputVertexTape).length + (base vertexCountTape).length + 2 =
      ((base vertexCountTape).length + 1) + ((base inputVertexTape).length + 1) by omega,
    Function.iterate_add_apply, h0]
  exact h1

theorem installTableTrace (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (base : (tape : Tape) → List (Alphabet tape))
    (newWord : List Bool) (resultWord : toBoolTapes base resultTape = newWord)
    (reverseEmpty : toBoolTapes base (.inr .tableReverse) = []) (state : State ρ d) :
    (advance (TM2.step (program positive H growth)))^[
        (toBoolTapes base tableTape).length + 2 * newWord.length +
          (toBoolTapes base (.inr .currentSize)).length + 4]
      (some ⟨some (.inr .clearOldTable), state, base⟩) =
      some ⟨some (.inr (.affine .multiplySize .seed)), clearRegister state,
        fromBoolTapes (installedTapes (toBoolTapes base) newWord)⟩ := by
  have h := installTableBoolTrace positive H growth (toBoolTapes base) newWord resultWord reverseEmpty state
  simpa only [configuration_fromBool, fromBool_toBool] using boolTraceActual positive H growth _ _ _ h

theorem cleanupCountersTrace (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (base : (tape : Tape) → List (Alphabet tape))
    (state : State ρ d) :
    (advance (TM2.step (program positive H growth)))^[
        (toBoolTapes base inputVertexTape).length + (toBoolTapes base vertexCountTape).length + 2]
      (some ⟨some (.inr .drainInputVertex), state, base⟩) =
      some ⟨some (.inr .levelGuard), clearRegister state,
        fromBoolTapes (cleanedCounterTapes (toBoolTapes base))⟩ := by
  have h := cleanupCountersBoolTrace positive H growth (toBoolTapes base) state
  simpa only [configuration_fromBool, fromBool_toBool] using boolTraceActual positive H growth _ _ _ h

def installTableInTime (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (base : (tape : Tape) → List (Alphabet tape))
    (newWord : List Bool) (resultWord : toBoolTapes base resultTape = newWord)
    (reverseEmpty : toBoolTapes base (.inr .tableReverse) = []) (state : State ρ d) :
    StateTransition.EvalsToInTime (TM2.step (program positive H growth))
      ⟨some (.inr .clearOldTable), state, base⟩
      (some ⟨some (.inr (.affine .multiplySize .seed)), clearRegister state,
        fromBoolTapes (installedTapes (toBoolTapes base) newWord)⟩)
      ((toBoolTapes base tableTape).length + 2 * newWord.length +
        (toBoolTapes base (.inr .currentSize)).length + 4) where
  steps := (toBoolTapes base tableTape).length + 2 * newWord.length +
    (toBoolTapes base (.inr .currentSize)).length + 4
  evals_in_steps := installTableTrace positive H growth base newWord resultWord reverseEmpty state
  steps_le_m := Nat.le_refl _

def cleanupCountersInTime (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (base : (tape : Tape) → List (Alphabet tape))
    (state : State ρ d) :
    StateTransition.EvalsToInTime (TM2.step (program positive H growth))
      ⟨some (.inr .drainInputVertex), state, base⟩
      (some ⟨some (.inr .levelGuard), clearRegister state,
        fromBoolTapes (cleanedCounterTapes (toBoolTapes base))⟩)
      ((toBoolTapes base inputVertexTape).length + (toBoolTapes base vertexCountTape).length + 2) where
  steps := (toBoolTapes base inputVertexTape).length + (toBoolTapes base vertexCountTape).length + 2
  evals_in_steps := cleanupCountersTrace positive H growth base state
  steps_le_m := Nat.le_refl _

end DFVSGames.Foundations.Complexity.MachineExpanderFamily
end

section

namespace DFVSGames.Foundations.Complexity.MachineExpanderFamily

open Turing MachineComposition
open PCP.ExpanderTables PCP.ExpanderRowControl

theorem affine_source_ne_scratch (phase : AffinePhase) :
    affineSource phase ≠ .inr .unaryScratch := by cases phase <;> decide

theorem affine_source_ne_destination (phase : AffinePhase) :
    affineSource phase ≠ affineDestination phase := by cases phase <;> decide

theorem affine_scratch_ne_destination (phase : AffinePhase) :
    (.inr .unaryScratch : Tape) ≠ affineDestination phase := by cases phase <;> decide

def affineResultTapes (d : Nat) (phase : AffinePhase)
    (base : (tape : Tape) → List (Alphabet tape)) (n : Nat) :
    (tape : Tape) → List (Alphabet tape) :=
  Function.update base (affineDestination phase)
    (boolWord (affineDestination phase)
      (encodeWord (affineCoefficient d phase * n) ++ toBoolTapes base (affineDestination phase)))

theorem affineResultTapes_other (d : Nat) (phase : AffinePhase)
    (base : (tape : Tape) → List (Alphabet tape)) (n : Nat) (tape : Tape)
    (different : tape ≠ affineDestination phase) :
    affineResultTapes d phase base n tape = base tape := by
  simp [affineResultTapes, different]

theorem affineResultTapes_source (d : Nat) (phase : AffinePhase)
    (base : (tape : Tape) → List (Alphabet tape)) (n : Nat) :
    affineResultTapes d phase base n (affineSource phase) = base (affineSource phase) :=
  affineResultTapes_other d phase base n _ (affine_source_ne_destination phase)

theorem affineResultTapes_scratch (d : Nat) (phase : AffinePhase)
    (base : (tape : Tape) → List (Alphabet tape)) (n : Nat) :
    affineResultTapes d phase base n (.inr .unaryScratch) = base (.inr .unaryScratch) :=
  affineResultTapes_other d phase base n _ (affine_scratch_ne_destination phase)

theorem affineResultTapes_destination (d : Nat) (phase : AffinePhase)
    (base : (tape : Tape) → List (Alphabet tape)) (n : Nat) :
    toBoolTapes (affineResultTapes d phase base n) (affineDestination phase) =
      encodeWord (affineCoefficient d phase * n) ++ toBoolTapes base (affineDestination phase) := by
  simp [affineResultTapes, toBoolTapes]

variable {ρ : Type} [Fintype ρ] {d : Nat}

theorem affinePhaseBoolTrace (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (phase : AffinePhase) (base : Tape → List Bool)
    (n : Nat) (suffix : List Bool)
    (sourceWord : base (affineSource phase) = encodeWord n ++ suffix)
    (scratchEmpty : base (.inr .unaryScratch) = []) (state : State ρ d) :
    (advance (TM2.step (boolView positive H growth)))^[2 * (n + 1) + 1]
      (some ⟨some (.inr (.affine phase .seed)), state, base⟩) =
      some ⟨some (affineExit d phase), clearRegister state,
        Function.update base (affineDestination phase)
          (encodeWord (affineCoefficient d phase * n) ++ base (affineDestination phase))⟩ := by
  let states := registerStates ρ d
  let target := boolView (ρ := ρ) positive H growth
  let sourceProgram := MachineControl.program (Equiv.refl (Label d)) states.symm target
  have atSeed : sourceProgram (.inr (.affine phase .seed)) =
      MachineUnaryAffineAt.seed (affineDestination phase) 0 (.inr (.affine phase .scan)) := by
    change MachineControl.statement id states.symm
      (boolView positive H growth (.inr (.affine phase .seed))) = _
    rw [boolView_outer]
    exact controlStatementInverse states _
  have atScan : sourceProgram (.inr (.affine phase .scan)) =
      MachineUnaryAffineAt.scan (affineSource phase) (.inr .unaryScratch)
        (affineDestination phase) (affineCoefficient d phase)
        (.inr (.affine phase .scan)) (.inr (.affine phase .restore)) := by
    change MachineControl.statement id states.symm
      (boolView positive H growth (.inr (.affine phase .scan))) = _
    rw [boolView_outer]
    exact controlStatementInverse states _
  have atRestore : sourceProgram (.inr (.affine phase .restore)) =
      Reduction.MachineTransfer.loopAt (.inr .unaryScratch) (affineSource phase) id false
        (.inr (.affine phase .restore)) (some (affineExit d phase)) := by
    change MachineControl.statement id states.symm
      (boolView positive H growth (.inr (.affine phase .restore))) = _
    rw [boolView_outer]
    exact controlStatementInverse states _
  have raw := MachineUnaryAffineAt.seededAffineTrace
    (affineSource phase) (.inr .unaryScratch) (affineDestination phase)
    (affine_source_ne_scratch phase) (affine_source_ne_destination phase)
    (affine_scratch_ne_destination phase) (affineCoefficient d phase) 0
    (.inr (.affine phase .seed)) (.inr (.affine phase .scan)) (.inr (.affine phase .restore))
    (some (affineExit d phase)) sourceProgram atSeed atScan atRestore base n suffix
    sourceWord scratchEmpty (states.symm state).1 (states.symm state).2
  have run := controlTrace states target (2 * (n + 1) + 1) _ _ raw
  simpa only [states, target, MachineControl.configuration, Option.map_some, id_eq, Prod.mk.eta,
    Equiv.apply_symm_apply, Nat.add_zero, registerStates_reset] using run

theorem affinePhaseTrace (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (phase : AffinePhase)
    (base : (tape : Tape) → List (Alphabet tape)) (n : Nat) (suffix : List Bool)
    (sourceWord : toBoolTapes base (affineSource phase) = encodeWord n ++ suffix)
    (scratchEmpty : base (.inr .unaryScratch) = []) (state : State ρ d) :
    (advance (TM2.step (program positive H growth)))^[2 * (n + 1) + 1]
      (some ⟨some (.inr (.affine phase .seed)), state, base⟩) =
      some ⟨some (affineExit d phase), clearRegister state,
        affineResultTapes d phase base n⟩ := by
  have raw := affinePhaseBoolTrace positive H growth phase (toBoolTapes base) n suffix
    sourceWord scratchEmpty state
  have transported := boolTraceActual positive H growth (2 * (n + 1) + 1) _ _ raw
  simpa only [configuration_fromBool, fromBoolTapes_update, fromBool_toBool,
    affineResultTapes] using transported

def affinePhaseInTime (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (phase : AffinePhase)
    (base : (tape : Tape) → List (Alphabet tape)) (n : Nat) (suffix : List Bool)
    (sourceWord : toBoolTapes base (affineSource phase) = encodeWord n ++ suffix)
    (scratchEmpty : base (.inr .unaryScratch) = []) (state : State ρ d) :
    StateTransition.EvalsToInTime (TM2.step (program positive H growth))
      ⟨some (.inr (.affine phase .seed)), state, base⟩
      (some ⟨some (affineExit d phase), clearRegister state,
        affineResultTapes d phase base n⟩) (2 * (n + 1) + 1) where
  steps := 2 * (n + 1) + 1
  evals_in_steps := affinePhaseTrace positive H growth phase base n suffix sourceWord scratchEmpty state
  steps_le_m := Nat.le_refl _

def copyCountInTime (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (base : (tape : Tape) → List (Alphabet tape))
    (n : Nat) (sourceWord : base (.inr .currentSize) = encodeWord n)
    (scratchEmpty : base (.inr .unaryScratch) = [])
    (destinationEmpty : base vertexCountTape = []) (state : State ρ d) :
    StateTransition.EvalsToInTime (TM2.step (program positive H growth))
      ⟨some (.inr (.affine .copyCount .seed)), state, base⟩
      (some ⟨some (.inl (.inr .initialize)), clearRegister state,
        Function.update base vertexCountTape (encodeWord n)⟩) (2 * (n + 1) + 1) := by
  have run := affinePhaseInTime positive H growth .copyCount base n []
    (by simpa only [affineSource, toBoolTapes, toBoolWord, List.append_nil] using sourceWord)
    scratchEmpty state
  change base (.inl (.inr .vertexCount)) = [] at destinationEmpty
  simpa only [affineExit, affineResultTapes, affineDestination, affineCoefficient,
    Nat.one_mul, vertexCountTape, boolWord, toBoolTapes, toBoolWord,
    destinationEmpty, List.append_nil] using run

def multiplySizeInTime (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (base : (tape : Tape) → List (Alphabet tape))
    (n : Nat) (sourceWord : base inputVertexTape = encodeWord n)
    (scratchEmpty : base (.inr .unaryScratch) = [])
    (destinationEmpty : base (.inr .currentSize) = []) (state : State ρ d) :
    StateTransition.EvalsToInTime (TM2.step (program positive H growth))
      ⟨some (.inr (.affine .multiplySize .seed)), state, base⟩
      (some ⟨some (.inr .drainInputVertex), clearRegister state,
        Function.update base (.inr .currentSize) (encodeWord (cloudSize d * n))⟩)
      (2 * (n + 1) + 1) := by
  have run := affinePhaseInTime positive H growth .multiplySize base n []
    (by simpa only [affineSource, inputVertexTape, toBoolTapes, toBoolWord,
      List.append_nil] using sourceWord)
    scratchEmpty state
  simpa only [affineExit, affineResultTapes, affineDestination, affineCoefficient,
    boolWord, toBoolTapes, toBoolWord, destinationEmpty, List.append_nil] using run

end DFVSGames.Foundations.Complexity.MachineExpanderFamily
end

section

namespace DFVSGames.Foundations.Complexity.MachineExpanderRow

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.AlphabetTable

def emitSteps (n : Nat) : Nat := 3 * (n + 1) + 6

theorem affinePlan_bits {σ : Type} {bound : Nat} (coefficient : Nat)
    (offset : σ → Fin bound) (n : Nat) (ambient : σ) :
    Emitter.prefixBits (affinePlan coefficient offset) (fun _ : Fin 1 => n) ambient 3 =
      encodeWord (coefficient * n + (offset ambient).val) := by
  change Emitter.prefixBits
    (Emitter.listCommands (Emitter.affineCommands [((0 : Fin 1), coefficient)] offset))
    (fun _ : Fin 1 => n) ambient
    (Emitter.affineCommands [((0 : Fin 1), coefficient)] offset).length = _
  rw [Emitter.bits_listCommands, Emitter.affineCommands_bits]
  simp [Emitter.affineValue]

theorem affinePlan_steps {σ : Type} {bound : Nat} (coefficient : Nat)
    (offset : σ → Fin bound) (n : Nat) :
    Emitter.prefixSteps (affinePlan coefficient offset) (fun _ : Fin 1 => n) 3 + 1 =
      emitSteps n := by
  simp [affinePlan, Emitter.prefixSteps, Emitter.commandAt, Emitter.listCommands,
    Emitter.affineCommands, Emitter.commandSteps, emitSteps]

def emittedWord {K : Type} [DecidableEq K]
    (target : K) (base : K → List Bool) (value : Nat) : K → List Bool :=
  Function.update base target ((encodeWord value).reverse ++ base target)

@[simp] theorem emittedWord_target {K : Type} [DecidableEq K]
    (target : K) (base : K → List Bool) (value : Nat) :
    emittedWord target base value target = (encodeWord value).reverse ++ base target := by
  simp [emittedWord]

theorem emittedWord_other {K : Type} [DecidableEq K]
    (target : K) (base : K → List Bool) (value : Nat)
    (tape : K) (different : tape ≠ target) :
    emittedWord target base value tape = base tape := by
  simp [emittedWord, different]

variable {ρ : Type} [Fintype ρ] {d : Nat}

@[simp] theorem program_firstEmit (positive : 0 < d) (H : Table (cloudSize d) d)
    (label : Emitter.Label 3 (degree d)) :
    program (ρ := ρ) positive H (.firstEmit label) =
      Emitter.statement (firstPlan ρ d) (fun _ : Fin 1 => Tape.inputVertex)
        .emitScratch .queryReverse Label.firstEmit (some Label.firstReverse) label := rfl

@[simp] theorem program_secondEmit (positive : 0 < d) (H : Table (cloudSize d) d)
    (label : Emitter.Label 3 (degree d)) :
    program (ρ := ρ) positive H (.secondEmit label) =
      Emitter.statement (secondPlan ρ d) (fun _ : Fin 1 => Tape.quotientFirst)
        .emitScratch .queryReverse Label.secondEmit (some Label.secondReverse) label := rfl

@[simp] theorem program_outputEmit (positive : 0 < d) (H : Table (cloudSize d) d)
    (label : Emitter.Label 3 (rowFactor d)) :
    program (ρ := ρ) positive H (.outputEmit label) =
      Emitter.statement (outputPlan ρ d) (fun _ : Fin 1 => Tape.quotientSecond)
        .emitScratch .output Label.outputEmit (some (Label.cleanup 0)) label := rfl

section Embedded

variable {K Λ : Type} [DecidableEq K]

theorem firstEmitTraceAt (positive : 0 < d) (H : Table (cloudSize d) d)
    (ports : Tape → K) (portsInjective : Function.Injective ports)
    (labels : Label d → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State ρ d))
    (atLabels : ∀ l, target (labels l) = statement positive H ports labels exit l)
    (n : Nat) (base : K → List Bool)
    (source : base (ports .inputVertex) = encodeWord n)
    (scratch : base (ports .emitScratch) = [])
    (ambient : Ambient ρ d × Fin (degree d)) :
    (MachineComposition.advance (TM2.step target))^[emitSteps n]
      (some ⟨some (labels (.firstEmit (Emitter.labelAt 3 _ 0 .entry))),
        ((ambient, ()), none), base⟩) =
      some ⟨some (labels .firstReverse), ((ambient, ()), none),
        emittedWord (ports .queryReverse) base (firstAddress n ambient.1.2)⟩ := by
  have code : ∀ l, target (labels (.firstEmit l)) =
      Emitter.statement (firstPlan ρ d) (fun _ : Fin 1 => ports .inputVertex)
        (ports .emitScratch) (ports .queryReverse) (fun k => labels (.firstEmit k))
        (some (labels .firstReverse)) l := by
    intro l
    rw [atLabels]
    rfl
  have run := Emitter.planTrace (firstPlan ρ d) (fun _ : Fin 1 => ports .inputVertex)
    (ports .emitScratch) (ports .queryReverse)
    (by intro i h; have h' := portsInjective h; cases h')
    (by intro i h; have h' := portsInjective h; cases h')
    (by intro h; have h' := portsInjective h; cases h')
    (fun k => labels (.firstEmit k)) (some (labels .firstReverse)) target code
    (fun _ : Fin 1 => n) base (fun _ => source) scratch ambient
  simpa only [firstPlan, affinePlan_steps, affinePlan_bits, Emitter.resultTapes,
    emittedWord, firstAddress] using run

theorem secondEmitTraceAt (positive : 0 < d) (H : Table (cloudSize d) d)
    (ports : Tape → K) (portsInjective : Function.Injective ports)
    (labels : Label d → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State ρ d))
    (atLabels : ∀ l, target (labels l) = statement positive H ports labels exit l)
    (n : Nat) (base : K → List Bool)
    (source : base (ports .quotientFirst) = encodeWord n)
    (scratch : base (ports .emitScratch) = [])
    (ambient : Ambient ρ d × Fin (degree d)) :
    (MachineComposition.advance (TM2.step target))^[emitSteps n]
      (some ⟨some (labels (.secondEmit (Emitter.labelAt 3 _ 0 .entry))),
        ((ambient, ()), none), base⟩) =
      some ⟨some (labels .secondReverse), ((ambient, ()), none),
        emittedWord (ports .queryReverse) base (secondAddress n ambient.1.2)⟩ := by
  have code : ∀ l, target (labels (.secondEmit l)) =
      Emitter.statement (secondPlan ρ d) (fun _ : Fin 1 => ports .quotientFirst)
        (ports .emitScratch) (ports .queryReverse) (fun k => labels (.secondEmit k))
        (some (labels .secondReverse)) l := by
    intro l
    rw [atLabels]
    rfl
  have run := Emitter.planTrace (secondPlan ρ d) (fun _ : Fin 1 => ports .quotientFirst)
    (ports .emitScratch) (ports .queryReverse)
    (by intro i h; have h' := portsInjective h; cases h')
    (by intro i h; have h' := portsInjective h; cases h')
    (by intro h; have h' := portsInjective h; cases h')
    (fun k => labels (.secondEmit k)) (some (labels .secondReverse)) target code
    (fun _ : Fin 1 => n) base (fun _ => source) scratch ambient
  simpa only [secondPlan, affinePlan_steps, affinePlan_bits, Emitter.resultTapes,
    emittedWord, secondAddress] using run

theorem outputEmitTraceAt (positive : 0 < d) (H : Table (cloudSize d) d)
    (ports : Tape → K) (portsInjective : Function.Injective ports)
    (labels : Label d → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State ρ d))
    (atLabels : ∀ l, target (labels l) = statement positive H ports labels exit l)
    (n : Nat) (base : K → List Bool)
    (source : base (ports .quotientSecond) = encodeWord n)
    (scratch : base (ports .emitScratch) = [])
    (ambient : Ambient ρ d × Fin (degree d)) :
    (MachineComposition.advance (TM2.step target))^[emitSteps n]
      (some ⟨some (labels (.outputEmit (Emitter.labelAt 3 _ 0 .entry))),
        ((ambient, ()), none), base⟩) =
      some ⟨some (labels (.cleanup 0)), ((ambient, ()), none),
        emittedWord (ports .output) base (outputAddress n ambient.1.2)⟩ := by
  have code : ∀ l, target (labels (.outputEmit l)) =
      Emitter.statement (outputPlan ρ d) (fun _ : Fin 1 => ports .quotientSecond)
        (ports .emitScratch) (ports .output) (fun k => labels (.outputEmit k))
        (some (labels (.cleanup 0))) l := by
    intro l
    rw [atLabels]
    rfl
  have run := Emitter.planTrace (outputPlan ρ d) (fun _ : Fin 1 => ports .quotientSecond)
    (ports .emitScratch) (ports .output)
    (by intro i h; have h' := portsInjective h; cases h')
    (by intro i h; have h' := portsInjective h; cases h')
    (by intro h; have h' := portsInjective h; cases h')
    (fun k => labels (.outputEmit k)) (some (labels (.cleanup 0))) target code
    (fun _ : Fin 1 => n) base (fun _ => source) scratch ambient
  simpa only [outputPlan, affinePlan_steps, affinePlan_bits, Emitter.resultTapes,
    emittedWord, outputAddress] using run

def firstEmitInTimeAt (positive : 0 < d) (H : Table (cloudSize d) d)
    (ports : Tape → K) (portsInjective : Function.Injective ports)
    (labels : Label d → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State ρ d))
    (atLabels : ∀ l, target (labels l) = statement positive H ports labels exit l)
    (n : Nat) (base : K → List Bool)
    (source : base (ports .inputVertex) = encodeWord n)
    (scratch : base (ports .emitScratch) = [])
    (ambient : Ambient ρ d × Fin (degree d)) :
    StateTransition.EvalsToInTime (TM2.step target)
      ⟨some (labels (.firstEmit (Emitter.labelAt 3 _ 0 .entry))), ((ambient, ()), none), base⟩
      (some ⟨some (labels .firstReverse), ((ambient, ()), none),
        emittedWord (ports .queryReverse) base (firstAddress n ambient.1.2)⟩) (emitSteps n) where
  steps := emitSteps n
  evals_in_steps := firstEmitTraceAt positive H ports portsInjective labels exit target atLabels
    n base source scratch ambient
  steps_le_m := Nat.le_refl _

def secondEmitInTimeAt (positive : 0 < d) (H : Table (cloudSize d) d)
    (ports : Tape → K) (portsInjective : Function.Injective ports)
    (labels : Label d → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State ρ d))
    (atLabels : ∀ l, target (labels l) = statement positive H ports labels exit l)
    (n : Nat) (base : K → List Bool)
    (source : base (ports .quotientFirst) = encodeWord n)
    (scratch : base (ports .emitScratch) = [])
    (ambient : Ambient ρ d × Fin (degree d)) :
    StateTransition.EvalsToInTime (TM2.step target)
      ⟨some (labels (.secondEmit (Emitter.labelAt 3 _ 0 .entry))), ((ambient, ()), none), base⟩
      (some ⟨some (labels .secondReverse), ((ambient, ()), none),
        emittedWord (ports .queryReverse) base (secondAddress n ambient.1.2)⟩) (emitSteps n) where
  steps := emitSteps n
  evals_in_steps := secondEmitTraceAt positive H ports portsInjective labels exit target atLabels
    n base source scratch ambient
  steps_le_m := Nat.le_refl _

def outputEmitInTimeAt (positive : 0 < d) (H : Table (cloudSize d) d)
    (ports : Tape → K) (portsInjective : Function.Injective ports)
    (labels : Label d → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State ρ d))
    (atLabels : ∀ l, target (labels l) = statement positive H ports labels exit l)
    (n : Nat) (base : K → List Bool)
    (source : base (ports .quotientSecond) = encodeWord n)
    (scratch : base (ports .emitScratch) = [])
    (ambient : Ambient ρ d × Fin (degree d)) :
    StateTransition.EvalsToInTime (TM2.step target)
      ⟨some (labels (.outputEmit (Emitter.labelAt 3 _ 0 .entry))), ((ambient, ()), none), base⟩
      (some ⟨some (labels (.cleanup 0)), ((ambient, ()), none),
        emittedWord (ports .output) base (outputAddress n ambient.1.2)⟩) (emitSteps n) where
  steps := emitSteps n
  evals_in_steps := outputEmitTraceAt positive H ports portsInjective labels exit target atLabels
    n base source scratch ambient
  steps_le_m := Nat.le_refl _

end Embedded

theorem firstEmitTrace (positive : 0 < d) (H : Table (cloudSize d) d)
    (n : Nat) (base : Tape → List Bool)
    (source : base .inputVertex = encodeWord n) (scratch : base .emitScratch = [])
    (ambient : Ambient ρ d × Fin (degree d)) :
    (MachineComposition.advance (TM2.step (program positive H)))^[emitSteps n]
      (some ⟨some (.firstEmit (Emitter.labelAt 3 _ 0 .entry)),
        ((ambient, ()), none), base⟩) =
      some ⟨some .firstReverse, ((ambient, ()), none),
        emittedWord .queryReverse base (firstAddress n ambient.1.2)⟩ := by
  exact firstEmitTraceAt positive H id Function.injective_id id none (program positive H)
    (fun _ => rfl) n base source scratch ambient

theorem secondEmitTrace (positive : 0 < d) (H : Table (cloudSize d) d)
    (n : Nat) (base : Tape → List Bool)
    (source : base .quotientFirst = encodeWord n) (scratch : base .emitScratch = [])
    (ambient : Ambient ρ d × Fin (degree d)) :
    (MachineComposition.advance (TM2.step (program positive H)))^[emitSteps n]
      (some ⟨some (.secondEmit (Emitter.labelAt 3 _ 0 .entry)),
        ((ambient, ()), none), base⟩) =
      some ⟨some .secondReverse, ((ambient, ()), none),
        emittedWord .queryReverse base (secondAddress n ambient.1.2)⟩ := by
  exact secondEmitTraceAt positive H id Function.injective_id id none (program positive H)
    (fun _ => rfl) n base source scratch ambient

theorem outputEmitTrace (positive : 0 < d) (H : Table (cloudSize d) d)
    (n : Nat) (base : Tape → List Bool)
    (source : base .quotientSecond = encodeWord n) (scratch : base .emitScratch = [])
    (ambient : Ambient ρ d × Fin (degree d)) :
    (MachineComposition.advance (TM2.step (program positive H)))^[emitSteps n]
      (some ⟨some (.outputEmit (Emitter.labelAt 3 _ 0 .entry)),
        ((ambient, ()), none), base⟩) =
      some ⟨some (.cleanup 0), ((ambient, ()), none),
        emittedWord .output base (outputAddress n ambient.1.2)⟩ := by
  exact outputEmitTraceAt positive H id Function.injective_id id none (program positive H)
    (fun _ => rfl) n base source scratch ambient

def firstEmitInTime (positive : 0 < d) (H : Table (cloudSize d) d)
    (n : Nat) (base : Tape → List Bool)
    (source : base .inputVertex = encodeWord n) (scratch : base .emitScratch = [])
    (ambient : Ambient ρ d × Fin (degree d)) :
    StateTransition.EvalsToInTime (TM2.step (program positive H))
      ⟨some (.firstEmit (Emitter.labelAt 3 _ 0 .entry)), ((ambient, ()), none), base⟩
      (some ⟨some .firstReverse, ((ambient, ()), none),
        emittedWord .queryReverse base (firstAddress n ambient.1.2)⟩) (emitSteps n) where
  steps := emitSteps n
  evals_in_steps := firstEmitTrace positive H n base source scratch ambient
  steps_le_m := Nat.le_refl _

def secondEmitInTime (positive : 0 < d) (H : Table (cloudSize d) d)
    (n : Nat) (base : Tape → List Bool)
    (source : base .quotientFirst = encodeWord n) (scratch : base .emitScratch = [])
    (ambient : Ambient ρ d × Fin (degree d)) :
    StateTransition.EvalsToInTime (TM2.step (program positive H))
      ⟨some (.secondEmit (Emitter.labelAt 3 _ 0 .entry)), ((ambient, ()), none), base⟩
      (some ⟨some .secondReverse, ((ambient, ()), none),
        emittedWord .queryReverse base (secondAddress n ambient.1.2)⟩) (emitSteps n) where
  steps := emitSteps n
  evals_in_steps := secondEmitTrace positive H n base source scratch ambient
  steps_le_m := Nat.le_refl _

def outputEmitInTime (positive : 0 < d) (H : Table (cloudSize d) d)
    (n : Nat) (base : Tape → List Bool)
    (source : base .quotientSecond = encodeWord n) (scratch : base .emitScratch = [])
    (ambient : Ambient ρ d × Fin (degree d)) :
    StateTransition.EvalsToInTime (TM2.step (program positive H))
      ⟨some (.outputEmit (Emitter.labelAt 3 _ 0 .entry)), ((ambient, ()), none), base⟩
      (some ⟨some (.cleanup 0), ((ambient, ()), none),
        emittedWord .output base (outputAddress n ambient.1.2)⟩) (emitSteps n) where
  steps := emitSteps n
  evals_in_steps := outputEmitTrace positive H n base source scratch ambient
  steps_le_m := Nat.le_refl _

end DFVSGames.Foundations.Complexity.MachineExpanderRow

end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
