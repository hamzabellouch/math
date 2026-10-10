import Mathlib
import OAI.Computability.DirectedFeedback.Machines.MachineStateEquiv

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

namespace DFVSGames.Foundations.Complexity.PoweringMachineLoop

open Turing

inductive HeaderTape
  | source | counter | vertices | darts
  deriving DecidableEq

instance : Fintype HeaderTape where
  elems := {.source, .counter, .vertices, .darts}
  complete tape := by cases tape <;> simp

inductive HeaderLabel
  | initialize | scan
  deriving DecidableEq

instance : Fintype HeaderLabel where
  elems := {.initialize, .scan}
  complete label := by cases label <;> simp

abbrev HeaderAlphabet (_ : HeaderTape) := Bool
abbrev HeaderState (σ : Type) := σ × Option Bool

def pushTrue {K Λ σ : Type} (destination : K) : Nat →
    TM2.Stmt (fun _ : K => Bool) Λ σ → TM2.Stmt (fun _ : K => Bool) Λ σ
  | 0, next => next
  | count + 1, next => pushTrue destination count (.push destination (fun _ => true) next)

theorem stepAux_pushTrue {K Λ σ : Type} [DecidableEq K]
    (destination : K) (count : Nat) (next : TM2.Stmt (fun _ : K => Bool) Λ σ)
    (state : σ) (tapes : K → List Bool) :
    TM2.stepAux (pushTrue destination count next) state tapes =
      TM2.stepAux next state
        (Function.update tapes destination (List.replicate count true ++ tapes destination)) := by
  induction count generalizing next with
  | zero => simp [pushTrue]
  | succ count ih =>
    rw [pushTrue, ih]
    simp [TM2.stepAux, List.replicate_succ, Function.update_idem]

theorem pushTrue_pushBound {K Λ σ : Type} (destination : K) (count : Nat)
    (next : TM2.Stmt (fun _ : K => Bool) Λ σ) :
    Runtime.statementPushBound (pushTrue destination count next) =
      count + Runtime.statementPushBound next := by
  induction count generalizing next with
  | zero => simp [pushTrue]
  | succ count ih => simp only [pushTrue, ih, Runtime.statementPushBound]; omega

def headerProgram {σ : Type} (B : Nat) :
    HeaderLabel → TM2.Stmt HeaderAlphabet HeaderLabel (HeaderState σ)
  | .initialize =>
      .push .counter (fun _ => false)
        (.push .vertices (fun _ => false)
          (.push .darts (fun _ => false)
            (.load (fun state => (state.1, none)) (.goto fun _ => .scan))))
  | .scan =>
      .pop .source (fun state head => (state.1, head))
        (.branch (fun state => state.2.getD false)
          (.push .counter (fun _ => true)
            (.push .vertices (fun _ => true)
              (pushTrue .darts B
                (.load (fun state => (state.1, none)) (.goto fun _ => .scan)))))
          (.load (fun state => (state.1, none)) .halt))

def headerMachine (B : Nat) : FinTM2 where
  K := HeaderTape
  k₀ := .source
  k₁ := .darts
  Γ := HeaderAlphabet
  Λ := HeaderLabel
  main := .initialize
  σ := HeaderState Unit
  initialState := ((), none)
  m := headerProgram B

def initialTapes (n : Nat) (suffix : List Bool) : HeaderTape → List Bool
  | .source => encodeWord n ++ suffix
  | _ => []

def scanTapes (B remaining processed : Nat) (suffix : List Bool) : HeaderTape → List Bool
  | .source => encodeWord remaining ++ suffix
  | .counter => encodeWord processed
  | .vertices => encodeWord processed
  | .darts => encodeWord (B * processed)

def finalTapes (B n : Nat) (suffix : List Bool) : HeaderTape → List Bool
  | .source => suffix
  | .counter => encodeWord n
  | .vertices => encodeWord n
  | .darts => encodeWord (B * n)

def scanConfiguration {σ : Type} (B remaining processed : Nat)
    (suffix : List Bool) (ambient : σ) (register : Option Bool) :
    TM2.Cfg HeaderAlphabet HeaderLabel (HeaderState σ) :=
  ⟨some .scan, (ambient, register), scanTapes B remaining processed suffix⟩

def finalConfiguration {σ : Type} (B n : Nat) (suffix : List Bool) (ambient : σ) :
    TM2.Cfg HeaderAlphabet HeaderLabel (HeaderState σ) :=
  ⟨none, (ambient, none), finalTapes B n suffix⟩

theorem initializeStep {σ : Type} (B n : Nat) (suffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    TM2.step (headerProgram B)
      ⟨some .initialize, (ambient, register), initialTapes n suffix⟩ =
        some (scanConfiguration B n 0 suffix ambient none) := by
  simp only [TM2.step, headerProgram, TM2.stepAux]
  congr 2
  funext tape
  cases tape <;> simp [initialTapes, scanTapes, encodeWord]

theorem scanStep_zero {σ : Type} (B processed : Nat) (suffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    TM2.step (headerProgram B) (scanConfiguration B 0 processed suffix ambient register) =
      some (finalConfiguration B processed suffix ambient) := by
  simp only [TM2.step, scanConfiguration, headerProgram, TM2.stepAux,
    scanTapes, encodeWord, List.replicate_zero, List.nil_append, List.singleton_append,
    List.head?_cons, List.tail_cons, Option.getD_some, Bool.cond_false]
  congr 2
  funext tape
  cases tape <;> simp [finalTapes, scanTapes]

theorem scanStep_succ {σ : Type} (B remaining processed : Nat) (suffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    TM2.step (headerProgram B)
      (scanConfiguration B (remaining + 1) processed suffix ambient register) =
      some (scanConfiguration B remaining (processed + 1) suffix ambient none) := by
  simp only [TM2.step, scanConfiguration, headerProgram, TM2.stepAux,
    scanTapes, encodeWord, List.replicate_succ, List.cons_append,
    List.head?_cons, List.tail_cons, Option.getD_some, Bool.cond_true]
  rw [stepAux_pushTrue]
  simp only [TM2.stepAux]
  congr 2
  funext tape
  cases tape <;>
    simp [scanTapes, encodeWord, Nat.mul_add, List.replicate_add,
      List.replicate_succ, List.append_assoc, Nat.add_comm,
      -List.replicate_append_replicate]

theorem scanTrace {σ : Type} (B remaining processed : Nat) (suffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step (headerProgram B)))^[remaining + 1]
      (some (scanConfiguration B remaining processed suffix ambient register)) =
      some (finalConfiguration B (processed + remaining) suffix ambient) := by
  induction remaining generalizing processed register with
  | zero =>
    simpa only [Nat.add_zero, Nat.zero_add, Function.iterate_one, MachineComposition.advance_some] using
      scanStep_zero B processed suffix ambient register
  | succ remaining ih =>
    rw [Function.iterate_succ_apply]
    change (MachineComposition.advance (TM2.step (headerProgram B)))^[remaining + 1]
      (TM2.step (headerProgram B)
        (scanConfiguration B (remaining + 1) processed suffix ambient register)) = _
    rw [scanStep_succ, ih]
    simp only [Nat.add_comm, Nat.add_left_comm]

theorem headerTrace {σ : Type} (B n : Nat) (suffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step (headerProgram B)))^[n + 2]
      (some ⟨some .initialize, (ambient, register), initialTapes n suffix⟩) =
      some (finalConfiguration B n suffix ambient) := by
  rw [show n + 2 = (n + 1) + 1 by omega, Function.iterate_succ_apply]
  change (MachineComposition.advance (TM2.step (headerProgram B)))^[n + 1]
    (TM2.step (headerProgram B)
      ⟨some .initialize, (ambient, register), initialTapes n suffix⟩) = _
  rw [initializeStep]
  simpa only [Nat.zero_add] using scanTrace B n 0 suffix ambient none

def headerInTime {σ : Type} (B n : Nat) (suffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step (headerProgram B))
      ⟨some .initialize, (ambient, register), initialTapes n suffix⟩
      (some (finalConfiguration B n suffix ambient)) (n + 2) where
  steps := n + 2
  evals_in_steps := headerTrace B n suffix ambient register
  steps_le_m := Nat.le_refl _

def remainingRows (rowBlock : Nat → List Bool) (n r : Nat) : List Bool :=
  (List.range' r (n - r)).flatMap rowBlock

@[simp] theorem remainingRows_top (rowBlock : Nat → List Bool) (n : Nat) :
    remainingRows rowBlock n n = [] := by simp [remainingRows]

theorem remainingRows_step (rowBlock : Nat → List Bool) (n r : Nat) (hr : r < n) :
    remainingRows rowBlock n r = rowBlock r ++ remainingRows rowBlock n (r + 1) := by
  have h : n - r = (n - (r + 1)) + 1 := by omega
  simp only [remainingRows, h, List.range'_succ, List.flatMap_cons]

section Enumeration

variable {K Λ σ : Type} [DecidableEq K]

def rowBase (output : K) (base : K → List Bool)
    (rowBlock : Nat → List Bool) (n r : Nat) : K → List Bool :=
  Function.update base output (remainingRows rowBlock n r ++ base output)

def VertexBodyTraces (counter output : K) (guardLabel bodyLabel : Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (σ × Option Bool))
    (base : K → List Bool) (suffix : List Bool) (ambient : σ)
    (rowBlock : Nat → List Bool) (cost : Nat → Nat) (n : Nat) : Prop :=
  ∀ r, r < n → ∀ accumulator : List Bool,
    (MachineComposition.advance (TM2.step program))^[cost r]
      (some ⟨some bodyLabel, (ambient, none),
        MachineUnaryCounter.counterTapes counter
          (Function.update base output accumulator) r suffix⟩) =
      some ⟨some guardLabel, (ambient, none),
        MachineUnaryCounter.counterTapes counter
          (Function.update base output (rowBlock r ++ accumulator)) r suffix⟩

theorem vertexBodyTraces_to_counted (counter output : K) (guardLabel bodyLabel : Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (σ × Option Bool))
    (base : K → List Bool) (suffix : List Bool) (ambient : σ)
    (rowBlock : Nat → List Bool) (cost : Nat → Nat) (n : Nat)
    (bodies : VertexBodyTraces counter output guardLabel bodyLabel program
      base suffix ambient rowBlock cost n) :
    MachineCountedLoop.BodyTraces counter guardLabel bodyLabel program suffix
      (fun _ => ambient) (fun _ => none) (rowBase output base rowBlock n) cost n := by
  intro r hr
  have h := bodies r hr (remainingRows rowBlock n (r + 1) ++ base output)
  simpa only [MachineCountedLoop.bodyConfiguration, MachineCountedLoop.guardConfiguration,
    rowBase, remainingRows_step rowBlock n r hr, List.append_assoc] using h

def vertexLoopInTime (counter output : K) (guardLabel bodyLabel exitLabel : Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (σ × Option Bool))
    (atGuard : program guardLabel = MachineUnaryCounter.guard counter bodyLabel exitLabel)
    (base : K → List Bool) (suffix : List Bool) (ambient : σ)
    (rowBlock : Nat → List Bool) (cost : Nat → Nat) (n bodyBound : Nat)
    (bodies : VertexBodyTraces counter output guardLabel bodyLabel program
      base suffix ambient rowBlock cost n)
    (bounded : ∀ r, r < n → cost r ≤ bodyBound) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some guardLabel, (ambient, none),
        MachineUnaryCounter.counterTapes counter base n suffix⟩
      (some ⟨some exitLabel, (ambient, none),
        MachineUnaryCounter.counterTapes counter
          (rowBase output base rowBlock n 0) 0 suffix⟩)
      (n * (bodyBound + 1) + 1) := by
  have h := MachineCountedLoop.loopInTime counter guardLabel bodyLabel exitLabel
    program atGuard suffix (fun _ => ambient) (fun _ => none)
    (rowBase output base rowBlock n) cost n bodyBound
    (vertexBodyTraces_to_counted counter output guardLabel bodyLabel program
      base suffix ambient rowBlock cost n bodies) bounded
  simpa [MachineCountedLoop.guardConfiguration, MachineCountedLoop.exitConfiguration,
    rowBase] using h

theorem vertexLoop_output (counter output : K) (different : output ≠ counter)
    (base : K → List Bool) (suffix : List Bool) (rowBlock : Nat → List Bool) (n : Nat) :
    MachineUnaryCounter.counterTapes counter (rowBase output base rowBlock n 0) 0 suffix output =
      remainingRows rowBlock n 0 ++ base output := by
  simp [MachineUnaryCounter.counterTapes, rowBase, different]

def varyingRowBase (output : K) (base : Nat → K → List Bool)
    (rowBlock : Nat → List Bool) (n r : Nat) : K → List Bool :=
  Function.update (base r) output (remainingRows rowBlock n r ++ base n output)

def VaryingVertexBodyTraces (counter output : K) (guardLabel bodyLabel : Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (σ × Option Bool))
    (base : Nat → K → List Bool) (suffix : List Bool) (ambient : Nat → σ)
    (rowBlock : Nat → List Bool) (cost : Nat → Nat) (n : Nat) : Prop :=
  ∀ r, r < n → ∀ accumulator : List Bool,
    (MachineComposition.advance (TM2.step program))^[cost r]
      (some ⟨some bodyLabel, (ambient (r + 1), none),
        MachineUnaryCounter.counterTapes counter
          (Function.update (base (r + 1)) output accumulator) r suffix⟩) =
      some ⟨some guardLabel, (ambient r, none),
        MachineUnaryCounter.counterTapes counter
          (Function.update (base r) output (rowBlock r ++ accumulator)) r suffix⟩

theorem varyingVertexBodyTraces_to_counted (counter output : K) (guardLabel bodyLabel : Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (σ × Option Bool))
    (base : Nat → K → List Bool) (suffix : List Bool) (ambient : Nat → σ)
    (rowBlock : Nat → List Bool) (cost : Nat → Nat) (n : Nat)
    (bodies : VaryingVertexBodyTraces counter output guardLabel bodyLabel program
      base suffix ambient rowBlock cost n) :
    MachineCountedLoop.BodyTraces counter guardLabel bodyLabel program suffix
      ambient (fun _ => none) (varyingRowBase output base rowBlock n) cost n := by
  intro r hr
  have h := bodies r hr (remainingRows rowBlock n (r + 1) ++ base n output)
  simpa only [MachineCountedLoop.bodyConfiguration, MachineCountedLoop.guardConfiguration,
    varyingRowBase, remainingRows_step rowBlock n r hr, List.append_assoc] using h

def vertexLoopInTime_varying (counter output : K) (guardLabel bodyLabel exitLabel : Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (σ × Option Bool))
    (atGuard : program guardLabel = MachineUnaryCounter.guard counter bodyLabel exitLabel)
    (base : Nat → K → List Bool) (suffix : List Bool) (ambient : Nat → σ)
    (rowBlock : Nat → List Bool) (cost : Nat → Nat) (n bodyBound : Nat)
    (bodies : VaryingVertexBodyTraces counter output guardLabel bodyLabel program
      base suffix ambient rowBlock cost n)
    (bounded : ∀ r, r < n → cost r ≤ bodyBound) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some guardLabel, (ambient n, none),
        MachineUnaryCounter.counterTapes counter (base n) n suffix⟩
      (some ⟨some exitLabel, (ambient 0, none),
        MachineUnaryCounter.counterTapes counter
          (varyingRowBase output base rowBlock n 0) 0 suffix⟩)
      (n * (bodyBound + 1) + 1) := by
  have h := MachineCountedLoop.loopInTime counter guardLabel bodyLabel exitLabel
    program atGuard suffix ambient (fun _ => none)
    (varyingRowBase output base rowBlock n) cost n bodyBound
    (varyingVertexBodyTraces_to_counted counter output guardLabel bodyLabel program
      base suffix ambient rowBlock cost n bodies) bounded
  simpa [MachineCountedLoop.guardConfiguration, MachineCountedLoop.exitConfiguration,
    varyingRowBase] using h

theorem vertexLoop_varying_output (counter output : K) (different : output ≠ counter)
    (base : Nat → K → List Bool) (suffix : List Bool)
    (rowBlock : Nat → List Bool) (n : Nat) :
    MachineUnaryCounter.counterTapes counter
        (varyingRowBase output base rowBlock n 0) 0 suffix output =
      remainingRows rowBlock n 0 ++ base n output := by
  simp [MachineUnaryCounter.counterTapes, varyingRowBase, different]

end Enumeration

end DFVSGames.Foundations.Complexity.PoweringMachineLoop
end

section

namespace DFVSGames.Foundations.Complexity.PoweringMasterState

open Turing
open MachineFixedBlockMap

abbrev OtherRegisters (N : Nat) := Buffer N × (Bool × Option Bool)
abbrev Master (N : Nat) := OtherRegisters N × Option Bool
abbrev CompareState (N : Nat) := Buffer N × (Bool × (Option Bool × Option Bool))
abbrev RowState (N : Nat) := (Bool × (Option Bool × Option Bool)) × Buffer N

def compareEquiv (N : Nat) : Master N ≃ CompareState N :=
  (MachineUnaryEqualityBit.compareStateEquiv (Buffer N)).symm

def rowEquiv (N : Nat) : Master N ≃ RowState N where
  toFun state := ((state.1.2.1, (state.1.2.2, state.2)), state.1.1)
  invFun state := ((state.2, (state.1.1, state.1.2.1)), state.1.2.2)
  left_inv := by rintro ⟨⟨buffer, ⟨flag, left⟩⟩, right⟩; rfl
  right_inv := by rintro ⟨⟨flag, ⟨left, right⟩⟩, buffer⟩; rfl

@[simp] theorem compareEquiv_apply (N : Nat) (buffer : Buffer N)
    (flag : Bool) (left right : Option Bool) :
    compareEquiv N ((buffer, (flag, left)), right) = (buffer, (flag, (left, right))) := rfl

@[simp] theorem compareEquiv_symm_apply (N : Nat) (buffer : Buffer N)
    (flag : Bool) (left right : Option Bool) :
    (compareEquiv N).symm (buffer, (flag, (left, right))) = ((buffer, (flag, left)), right) := rfl

@[simp] theorem rowEquiv_apply (N : Nat) (buffer : Buffer N)
    (flag : Bool) (left right : Option Bool) :
    rowEquiv N ((buffer, (flag, left)), right) = ((flag, (left, right)), buffer) := rfl

@[simp] theorem rowEquiv_symm_apply (N : Nat) (buffer : Buffer N)
    (flag : Bool) (left right : Option Bool) :
    (rowEquiv N).symm ((flag, (left, right)), buffer) = ((buffer, (flag, left)), right) := rfl

def withBuffer {N : Nat} (buffer : Buffer N) : Master N :=
  ((buffer, (false, none)), none)

def clean (N : Nat) : Master N := withBuffer (emptyBuffer N)

@[simp] theorem equalityBit_clean {N : Nat} (buffer : Buffer N) :
    MachineUnaryEqualityBit.clean buffer = withBuffer buffer := rfl

@[simp] theorem rowEquiv_withBuffer {N : Nat} (buffer : Buffer N) :
    rowEquiv N (withBuffer buffer) = ((false, (none, none)), buffer) := rfl

@[simp] theorem compareEquiv_withBuffer {N : Nat} (buffer : Buffer N) :
    compareEquiv N (withBuffer buffer) = (buffer, (false, (none, none))) := rfl

def clearBuffer {N : Nat} (state : Master N) : Master N :=
  (rowEquiv N).symm ((rowEquiv N state).1, emptyBuffer N)

@[simp] theorem clearBuffer_apply {N : Nat} (buffer : Buffer N)
    (flag : Bool) (left right : Option Bool) :
    clearBuffer ((buffer, (flag, left)), right) =
      ((emptyBuffer N, (flag, left)), right) := rfl

@[simp] theorem clearBuffer_withBuffer {N : Nat} (buffer : Buffer N) :
    clearBuffer (withBuffer buffer) = clean N := rfl

section Row

variable {K Λ : Type} [DecidableEq K] {N M : Nat}

def encodedBlockAt (src dst : K) (F : Buffer N → Buffer M) (exit : Option Λ) :
    TM2.Stmt (fun _ : K => Bool) Λ (Master N) :=
  MachineStateEquiv.statement (rowEquiv N).symm
    (PoweringMachineRow.encodedBlockAt src dst F exit)

theorem stepAux_encodedBlockAt (src dst : K) (F : Buffer N → Buffer M)
    (exit : Option Λ) (hne : src ≠ dst) (bits : Buffer N) (suffix : List Bool)
    (state : Master N) (tapes : K → List Bool)
    (hinput : tapes src = PoweringMachineRow.encodeBits (List.ofFn bits) ++ suffix) :
    TM2.stepAux (encodedBlockAt src dst F exit) state tapes =
      { l := exit, var := clearBuffer state,
        stk := Function.update (Function.update tapes src suffix) dst
          (PoweringMachineRow.encodeBits (List.ofFn (F bits)) ++ tapes dst) } := by
  rw [encodedBlockAt, MachineStateEquiv.stepAux_transport_symm, Equiv.symm_symm]
  rw [PoweringMachineRow.stepAux_encodedBlockAt src dst F exit hne bits suffix
    (rowEquiv N state) tapes hinput]
  rfl

theorem step_encodedBlockAt (src dst : K) (F : Buffer N → Buffer M) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (Master N))
    (label : Λ) (atLabel : program label = encodedBlockAt src dst F exit)
    (hne : src ≠ dst) (bits : Buffer N) (suffix : List Bool)
    (state : Master N) (tapes : K → List Bool)
    (hinput : tapes src = PoweringMachineRow.encodeBits (List.ofFn bits) ++ suffix) :
    TM2.step program ⟨some label, state, tapes⟩ =
      some ⟨exit, clearBuffer state,
        Function.update (Function.update tapes src suffix) dst
          (PoweringMachineRow.encodeBits (List.ofFn (F bits)) ++ tapes dst)⟩ := by
  simp only [TM2.step, atLabel, stepAux_encodedBlockAt src dst F exit hne bits suffix state tapes hinput]

def rowAt {t S q : Nat} (src dst : K)
    (labelAt : Fin q → Fin S → PCP.GraphTables.Label) (exit : Option Λ) :
    TM2.Stmt (fun _ : K => Bool) Λ (Master (PoweringMachineRow.inputSize t S)) :=
  encodedBlockAt src dst (PoweringMachineRow.rowBlock labelAt) exit

theorem step_rowAt_clean {t S q : Nat} (src dst : K)
    (labelAt : Fin q → Fin S → PCP.GraphTables.Label) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ
      (Master (PoweringMachineRow.inputSize t S)))
    (label : Λ) (atLabel : program label = rowAt (t := t) src dst labelAt exit)
    (hne : src ≠ dst) (bits register : Buffer (PoweringMachineRow.inputSize t S))
    (suffix : List Bool) (tapes : K → List Bool)
    (hinput : tapes src = PoweringMachineRow.encodeBits (List.ofFn bits) ++ suffix) :
    TM2.step program ⟨some label, withBuffer register, tapes⟩ =
      some ⟨exit, clean (PoweringMachineRow.inputSize t S),
        Function.update (Function.update tapes src suffix) dst
          (PoweringMachineRow.encodeBits (List.ofFn (PoweringMachineRow.rowBlock labelAt bits)) ++
            tapes dst)⟩ := by
  simpa only [rowAt, clearBuffer_withBuffer] using
    step_encodedBlockAt src dst (PoweringMachineRow.rowBlock labelAt) exit
      program label atLabel hne bits suffix (withBuffer register) tapes hinput

def rowInTime {t S q : Nat} (src dst : K)
    (labelAt : Fin q → Fin S → PCP.GraphTables.Label) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ
      (Master (PoweringMachineRow.inputSize t S)))
    (label : Λ) (atLabel : program label = rowAt (t := t) src dst labelAt exit)
    (hne : src ≠ dst) (bits register : Buffer (PoweringMachineRow.inputSize t S))
    (suffix : List Bool) (tapes : K → List Bool)
    (hinput : tapes src = PoweringMachineRow.encodeBits (List.ofFn bits) ++ suffix) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some label, withBuffer register, tapes⟩
      (some ⟨exit, clean (PoweringMachineRow.inputSize t S),
        Function.update (Function.update tapes src suffix) dst
          (PoweringMachineRow.encodeBits (List.ofFn (PoweringMachineRow.rowBlock labelAt bits)) ++
            tapes dst)⟩) 1 where
  steps := 1
  evals_in_steps := by
    simpa only [Function.iterate_one, flip, bind, Option.bind] using
      step_rowAt_clean src dst labelAt exit program label atLabel hne bits register suffix tapes hinput
  steps_le_m := le_rfl

end Row

def headerInTime (N B n : Nat) (suffix : List Bool) (state : Master N) :
    StateTransition.EvalsToInTime
      (TM2.step (PoweringMachineLoop.headerProgram (σ := OtherRegisters N) B))
      ⟨some .initialize, state, PoweringMachineLoop.initialTapes n suffix⟩
      (some (PoweringMachineLoop.finalConfiguration B n suffix state.1)) (n + 2) :=
  PoweringMachineLoop.headerInTime B n suffix state.1 state.2

end DFVSGames.Foundations.Complexity.PoweringMasterState
end

section

namespace DFVSGames.Foundations.PCP.PortTableLookup

private theorem flatMap_word_inline_PortTableLookup {α β : Type*} (f : α → List β)
    (width j : Nat) (hj : j < width) :
    ∀ (rows : List α), (∀ a ∈ rows, (f a).length = width) →
      ∀ (i : Nat) (row : α), rows[i]? = some row →
        (rows.flatMap f)[width * i + j]? = (f row)[j]? := by
  intro rows
  induction rows with
  | nil =>
      intro _ i row selected
      simp at selected
  | cons a rows ih =>
      intro hwidth i row selected
      have ha : (f a).length = width := hwidth a (by simp)
      cases i with
      | zero =>
          have heq : a = row := by simpa using selected
          subst row
          simp only [Nat.mul_zero, Nat.zero_add, List.flatMap_cons]
          exact List.getElem?_append_left (by omega)
      | succ i =>
          have selected' : rows[i]? = some row := by simpa using selected
          have hskip : (f a).length ≤ width * (i + 1) + j := by
            rw [ha, Nat.mul_add, Nat.mul_one]
            omega
          have hoff : width * (i + 1) + j - (f a).length = width * i + j := by
            rw [ha, Nat.mul_add, Nat.mul_one]
            omega
          rw [List.flatMap_cons, List.getElem?_append_right hskip, hoff]
          exact ih (fun b hb => hwidth b (by simp [hb])) i row selected'

variable {n d : Nat}

theorem vertices_word (table : PortTables.Table n d) :
    (PortTables.tableWords table)[0]? = some n := rfl

theorem darts_word (table : PortTables.Table n d) :
    (PortTables.tableWords table)[1]? = some (n * d) := rfl

private theorem row_word_inline_PortTableLookup (table : PortTables.Table n d) (i : Fin (n * d))
    (j : Nat) (hj : j < 4098) :
    (PortTables.tableWords table)[2 + 4098 * i.val + j]? =
      (GraphTables.rowWords (PortTables.flatRows table)[i])[j]? := by
  rw [PortTables.tableWords_eq]
  change (n :: n * d :: (PortTables.flatRows table).toList.flatMap
    GraphTables.rowWords)[2 + 4098 * i.val + j]? = _
  rw [show 2 + 4098 * i.val + j = (4098 * i.val + j + 1) + 1 by omega,
    List.getElem?_cons_succ, List.getElem?_cons_succ]
  apply flatMap_word_inline_PortTableLookup GraphTables.rowWords 4098 j hj
    (PortTables.flatRows table).toList
    (fun row _ => GraphTables.rowWords_length row) i.val
    ((PortTables.flatRows table)[i])
  simp only [Vector.getElem?_toList, Vector.getElem?_eq_getElem i.isLt,
    Fin.getElem_fin]

theorem tail_word (table : PortTables.Table n d) (i : Fin (n * d)) :
    (PortTables.tableWords table)[2 + 4098 * i.val]? =
      some (((PortTables.rowIndex n d).symm i).1.val) := by
  have h := row_word_inline_PortTableLookup table i 0 (by decide)
  simpa only [Nat.add_zero, GraphTables.rowWords, PortTables.flatRows,
    Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta, List.cons_append,
    List.nil_append, List.getElem?_cons_zero] using h

theorem reverse_word (table : PortTables.Table n d) (i : Fin (n * d)) :
    (PortTables.tableWords table)[3 + 4098 * i.val]? =
      some (table.reverseIndex[i].val) := by
  have h := row_word_inline_PortTableLookup table i 1 (by decide)
  rw [show 2 + 4098 * i.val + 1 = 3 + 4098 * i.val by omega] at h
  simpa only [GraphTables.rowWords, PortTables.flatRows, Fin.getElem_fin,
    Vector.getElem_ofFn, Fin.eta, List.cons_append, List.nil_append,
    List.getElem?_cons_succ, List.getElem?_cons_zero] using h

theorem relation_word (table : PortTables.Table n d) (i : Fin (n * d))
    (j : Fin 4096) :
    (PortTables.tableWords table)[4 + 4098 * i.val + j.val]? =
      some (GraphTables.bitWord table.relations[i][j]) := by
  have h := row_word_inline_PortTableLookup table i (j.val + 2) (by omega)
  rw [show 2 + 4098 * i.val + (j.val + 2) = 4 + 4098 * i.val + j.val by omega] at h
  simpa only [GraphTables.rowWords, GraphTables.relationWords,
    PortTables.flatRows, Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta,
    List.cons_append, List.nil_append, List.getElem?_cons_succ,
    List.getElem?_map, Vector.getElem?_toList,
    Vector.getElem?_eq_getElem j.isLt, Option.map_some] using h

theorem accepts_word (table : PortTables.Table n d) (e : Fin n × Fin d)
    (a b : PortTables.Label) :
    (PortTables.tableWords table)[4 + 4098 * (PortTables.rowIndex n d e).val +
        (GraphTables.relationIndex (a, b)).val]? =
      some (GraphTables.bitWord (PortTables.accepts table e a b)) :=
  relation_word table (PortTables.rowIndex n d e) (GraphTables.relationIndex (a, b))

theorem rotation_head_word (table : PortTables.Table n d) (e : Fin n × Fin d) :
    (PortTables.tableWords table)[2 + 4098 * (table.reverseIndex[PortTables.rowIndex n d e]).val]? =
      some ((PortTables.rotation table e).1.val) :=
  tail_word table (table.reverseIndex[PortTables.rowIndex n d e])

theorem rotor_lookups (table : PortTables.Table n d) (e : Fin n × Fin d) :
    (PortTables.tableWords table)[3 + 4098 * (PortTables.rowIndex n d e).val]? =
      some (table.reverseIndex[PortTables.rowIndex n d e].val) ∧
    (PortTables.tableWords table)[2 + 4098 * (table.reverseIndex[PortTables.rowIndex n d e]).val]? =
      some ((PortTables.rotation table e).1.val) :=
  ⟨reverse_word table (PortTables.rowIndex n d e), rotation_head_word table e⟩

end DFVSGames.Foundations.PCP.PortTableLookup
end

section

namespace DFVSGames.Foundations.Complexity.PoweringMachineRotor

open Turing
open MachineComposition
open PCP

variable {K Λ σ : Type} [DecidableEq K]
variable {n d : Nat}

abbrev Alphabet (_ : K) := Bool

def reverseRole (i : Fin 5) : Fin 7 :=
  if i = 0 then 0 else if i = 1 then 2 else if i = 2 then 3 else if i = 3 then 4 else 6

def endpointRole (i : Fin 5) : Fin 7 :=
  if i = 0 then 0 else if i = 1 then 2 else if i = 2 then 3 else if i = 3 then 5 else 6

theorem reverseRole_injective : Function.Injective reverseRole := by decide
theorem endpointRole_injective : Function.Injective endpointRole := by decide
theorem source_outside_reverse : ∀ i, (1 : Fin 7) ≠ reverseRole i := by decide
theorem reverse_outside_endpoint : ∀ i, (4 : Fin 7) ≠ endpointRole i := by decide

def reverseTapes (tape : Fin 7 → K) : Fin 5 → K := tape ∘ reverseRole
def endpointTapes (tape : Fin 7 → K) : Fin 5 → K := tape ∘ endpointRole

inductive Label
  | reverse (l : MachineAffineLookup.Label)
  | endpoint (l : MachineAffineLookup.Label)
  deriving DecidableEq, Fintype

def instruction (tape : Fin 7 → K) (degree port : Nat)
    (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool)
  | .reverse l => MachineAffineLookup.instruction (tape 1) (reverseTapes tape)
      (4098 * degree) (4098 * port + 3) (fun q => labels (.reverse q))
      (some (labels (.endpoint .seed))) l
  | .endpoint l => MachineAffineLookup.instruction (tape 4) (endpointTapes tape)
      4098 2 (fun q => labels (.endpoint q)) exit l

def reverseId (table : PortTables.Table n d) (vertex : Fin n) (port : Fin d) : Nat :=
  table.reverseIndex[PortTables.rowIndex n d (vertex, port)].val

def reverseAddress (vertex : Fin n) (port : Fin d) : Nat :=
  (4098 * d) * vertex.val + (4098 * port.val + 3)

def endpointAddress (table : PortTables.Table n d) (vertex : Fin n) (port : Fin d) : Nat :=
  4098 * reverseId table vertex port + 2

theorem reverse_selected (table : PortTables.Table n d) (vertex : Fin n) (port : Fin d) :
    (PortTables.tableWords table)[reverseAddress vertex port]? =
      some (reverseId table vertex port) := by
  have h := PortTableLookup.reverse_word table (PortTables.rowIndex n d (vertex, port))
  have hindex : reverseAddress vertex port = 3 + 4098 * (PortTables.rowIndex n d (vertex, port)).val := by
    simp only [reverseAddress, PortTables.rowIndex_val, Nat.mul_add, Nat.mul_assoc]
    omega
  rw [hindex]
  exact h

theorem endpoint_selected (table : PortTables.Table n d) (vertex : Fin n) (port : Fin d) :
    (PortTables.tableWords table)[endpointAddress table vertex port]? =
      some ((PortTables.rotation table (vertex, port)).1.val) := by
  have h := PortTableLookup.rotation_head_word table (vertex, port)
  simpa only [endpointAddress, reverseId, Nat.add_comm] using h

def afterReverse (tape : Fin 7 → K) (table : PortTables.Table n d)
    (vertex : Fin n) (port : Fin d) (base : K → List Bool) : K → List Bool :=
  MachineAffineLookup.finalTapes (reverseTapes tape) base (PortTables.tableWords table)
    (reverseAddress vertex port) (reverseId table vertex port)

def finalTapes (tape : Fin 7 → K) (table : PortTables.Table n d)
    (vertex : Fin n) (port : Fin d) (base : K → List Bool) : K → List Bool :=
  MachineAffineLookup.finalTapes (endpointTapes tape)
    (afterReverse tape table vertex port base) (PortTables.tableWords table)
    (endpointAddress table vertex port) ((PortTables.rotation table (vertex, port)).1.val)

def steps (table : PortTables.Table n d) (vertex : Fin n) (port : Fin d) : Nat :=
  MachineAffineLookup.steps (PortTables.tableWords table) vertex.val (4098 * d) (4098 * port.val + 3) +
    MachineAffineLookup.steps (PortTables.tableWords table) (reverseId table vertex port) 4098 2

theorem rotorTrace (tape : Fin 7 → K) (distinct : Function.Injective tape)
    (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (port : Fin d)
    (atLabels : ∀ l, program (labels l) = instruction tape d port.val labels exit l)
    (table : PortTables.Table n d) (vertex : Fin n) (base : K → List Bool)
    (tableWord : base (tape 0) = PortTables.tableBits table)
    (scratchEmpty : base (tape 6) = []) (suffix : List Bool)
    (sourceWord : base (tape 1) = encodeWord vertex.val ++ suffix)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[steps table vertex port]
      (some ⟨some (labels (.reverse .seed)), (ambient,register), base⟩) =
      some ⟨exit, (ambient,none), finalTapes tape table vertex port base⟩ := by
  have hd (i j : Fin 7) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  have hrDistinct : Function.Injective (reverseTapes tape) := distinct.comp reverseRole_injective
  have heDistinct : Function.Injective (endpointTapes tape) := distinct.comp endpointRole_injective
  have hrOutside : ∀ i, tape 1 ≠ reverseTapes tape i := fun i =>
    hd 1 (reverseRole i) (source_outside_reverse i)
  have heOutside : ∀ i, tape 4 ≠ endpointTapes tape i := fun i =>
    hd 4 (endpointRole i) (reverse_outside_endpoint i)
  have hreverse := MachineAffineLookup.affineLookupTrace (tape 1) (reverseTapes tape)
    hrDistinct hrOutside (4098 * d) (4098 * port.val + 3)
    (fun q => labels (.reverse q)) (some (labels (.endpoint .seed)))
    program (fun q => atLabels (.reverse q)) base (PortTables.tableWords table)
    tableWord scratchEmpty vertex.val suffix sourceWord (reverseId table vertex port)
    (reverse_selected table vertex port) ambient register
  let mid := afterReverse tape table vertex port base
  have hmidTable : mid (tape 0) = PortTables.tableBits table := by
    calc
      mid (tape 0) = base (tape 0) :=
        MachineAffineLookup.finalTapes_other _ _ _ _ _ _
          (hd 0 2 (by decide)) (hd 0 3 (by decide)) (hd 0 4 (by decide))
      _ = _ := tableWord
  have hmidScratch : mid (tape 6) = [] := by
    calc
      mid (tape 6) = base (tape 6) :=
        MachineAffineLookup.finalTapes_other _ _ _ _ _ _
          (hd 6 2 (by decide)) (hd 6 3 (by decide)) (hd 6 4 (by decide))
      _ = _ := scratchEmpty
  have hmidSource : mid (tape 4) = encodeWord (reverseId table vertex port) ++ base (tape 4) :=
    MachineAffineLookup.finalTapes_output _ _ _ _ _
  have hendpoint := MachineAffineLookup.affineLookupTrace (tape 4) (endpointTapes tape)
    heDistinct heOutside 4098 2 (fun q => labels (.endpoint q)) exit
    program (fun q => atLabels (.endpoint q)) mid (PortTables.tableWords table)
    hmidTable hmidScratch (reverseId table vertex port) (base (tape 4)) hmidSource
    ((PortTables.rotation table (vertex, port)).1.val)
    (endpoint_selected table vertex port) ambient none
  rw [steps, Nat.add_comm, Function.iterate_add_apply, hreverse]
  exact hendpoint

theorem finalTapes_endpoint (tape : Fin 7 → K) (distinct : Function.Injective tape)
    (table : PortTables.Table n d) (vertex : Fin n) (port : Fin d) (base : K → List Bool) :
    finalTapes tape table vertex port base (tape 5) =
      encodeWord ((PortTables.rotation table (vertex, port)).1.val) ++ base (tape 5) := by
  have hd (i j : Fin 7) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  change MachineAffineLookup.finalTapes (endpointTapes tape) _ _ _ _ (endpointTapes tape 3) = _
  rw [MachineAffineLookup.finalTapes_output]
  congr 1
  exact MachineAffineLookup.finalTapes_other _ _ _ _ _ _
    (hd 5 2 (by decide)) (hd 5 3 (by decide)) (hd 5 4 (by decide))

theorem finalTapes_other (tape : Fin 7 → K) (table : PortTables.Table n d)
    (vertex : Fin n) (port : Fin d) (base : K → List Bool) (k : K)
    (h₂ : k ≠ tape 2) (h₃ : k ≠ tape 3) (h₄ : k ≠ tape 4) (h₅ : k ≠ tape 5) :
    finalTapes tape table vertex port base k = base k := by
  calc
    finalTapes tape table vertex port base k = afterReverse tape table vertex port base k :=
      MachineAffineLookup.finalTapes_other _ _ _ _ _ _ h₂ h₃ h₅
    _ = base k := MachineAffineLookup.finalTapes_other _ _ _ _ _ _ h₂ h₃ h₄

theorem steps_le (table : PortTables.Table n d) (vertex : Fin n) (port : Fin d) :
    steps table vertex port ≤ 14 * (PortTables.tableBits table).length + 12 := by
  have hvertex : vertex.val ≤ (encodeWords (PortTables.tableWords table)).length :=
    Nat.le_trans (Nat.le_of_lt vertex.isLt) (PortTables.vertices_le_tableBits_length table)
  have hreverse := MachineLookupSpec.output_length_le (PortTables.tableWords table)
    (reverseAddress vertex port) (reverseId table vertex port) (reverse_selected table vertex port)
  rw [encodeWord_length] at hreverse
  have hr := MachineAffineLookup.steps_le_table (PortTables.tableWords table)
    vertex.val (4098 * d) (4098 * port.val + 3) (reverseId table vertex port)
    (reverse_selected table vertex port) hvertex
  have he := MachineAffineLookup.steps_le_table (PortTables.tableWords table)
    (reverseId table vertex port) 4098 2 ((PortTables.rotation table (vertex, port)).1.val)
    (endpoint_selected table vertex port) (by omega)
  change _ ≤ 14 * (encodeWords (PortTables.tableWords table)).length + 12
  unfold steps
  omega

def machine (degree port : Nat) : FinTM2 where
  K := Fin 7
  k₀ := 0
  k₁ := 5
  Γ _ := Bool
  Λ := Label
  main := .reverse .seed
  σ := Unit × Option Bool
  initialState := ((),none)
  m := instruction id degree port id none

end DFVSGames.Foundations.Complexity.PoweringMachineRotor
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
