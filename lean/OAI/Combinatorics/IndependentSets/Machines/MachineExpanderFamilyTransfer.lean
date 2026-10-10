import Mathlib
import OAI.Combinatorics.IndependentSets.Machines.MachineExpanderFamilyTapes

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.MachineExpanderFamily

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

end IndependentSetsGames.Foundations.Complexity.MachineExpanderFamily

end OAI
