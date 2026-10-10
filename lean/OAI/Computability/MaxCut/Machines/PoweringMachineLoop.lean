import Mathlib
import OAI.Computability.MaxCut.Machines.MachineSubroutine

namespace OAI

/-! Actual finite-control preparation and enumeration for the powered-table
machine. The degree and radius determine a fixed multiplier `B = 2*d^t`.
Only the input vertex count varies at runtime, and it is stored on unary
tapes. The header machine consumes a cloned first input field, preserving
its unread suffix, and writes the three fields needed by the outer loop.

The row enumeration lemmas specify the canonical suffix invariant used with
`MachineCountedLoop`. They do not stand in for the caller's per-row machine
traces, which must be supplied by the actual walk and relation evaluator. -/

namespace MaxCutGames.Foundations.Complexity.PoweringMachineLoop

open Turing

inductive HeaderTape
  | source | counter | vertices | darts
  deriving DecidableEq

protected abbrev HeaderTape.enumList : List HeaderTape := [.source, .counter, .vertices,
  .darts]

protected theorem HeaderTape.enumList_getElem?_ctorIdx_eq (x : HeaderTape) :
    HeaderTape.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem HeaderTape.enumList_nodup : HeaderTape.enumList.Nodup := by decide

instance : Fintype HeaderTape where
  elems := ⟨HeaderTape.enumList, HeaderTape.enumList_nodup⟩
  complete x := by cases x <;> decide

inductive HeaderLabel
  | initialize | scan
  deriving DecidableEq

protected abbrev HeaderLabel.enumList : List HeaderLabel := [.initialize, .scan]

protected theorem HeaderLabel.enumList_getElem?_ctorIdx_eq (x : HeaderLabel) :
    HeaderLabel.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem HeaderLabel.enumList_nodup : HeaderLabel.enumList.Nodup := by decide

instance : Fintype HeaderLabel where
  elems := ⟨HeaderLabel.enumList, HeaderLabel.enumList_nodup⟩
  complete x := by cases x <;> decide

abbrev HeaderAlphabet (_ : HeaderTape) := Bool
abbrev HeaderState (σ : Type) := σ × Option Bool

/-- A syntactic chain of a fixed number of true-bit pushes. -/
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

/-- Each true bit from the first input field contributes one counter bit,
one vertex-header bit, and `B` dart-header bits. No numeric register is used. -/
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

/-- The loop consumes precisely the unary field, including its delimiter. -/
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

/-- A genuine finite TM2 execution certificate for the header phase. -/
def headerInTime {σ : Type} (B n : Nat) (suffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step (headerProgram B))
      ⟨some .initialize, (ambient, register), initialTapes n suffix⟩
      (some (finalConfiguration B n suffix ambient)) (n + 2) where
  steps := n + 2
  evals_in_steps := headerTrace B n suffix ambient register
  steps_le_m := Nat.le_refl _

/-- Completed rows at guard remainder `r` are precisely vertices `r,...,n-1`.
This is a semantic description of the output tape, not a machine instruction. -/
def remainingRows (rowBlock : Nat → List Bool) (n r : Nat) : List Bool :=
  (List.range' r (n - r)).flatMap rowBlock

@[simp] theorem remainingRows_top (rowBlock : Nat → List Bool) (n : Nat) :
    remainingRows rowBlock n n = [] := by simp [remainingRows]

theorem remainingRows_step (rowBlock : Nat → List Bool) (n r : Nat) (hr : r < n) :
    remainingRows rowBlock n r = rowBlock r ++ remainingRows rowBlock n (r + 1) := by
  have h : n - r = (n - (r + 1)) + 1 := by omega
  simp only [remainingRows, h, List.range'_succ, List.flatMap_cons]

variable {K Λ σ : Type} [DecidableEq K]

def rowBase (output : K) (base : K → List Bool)
    (rowBlock : Nat → List Bool) (n r : Nat) : K → List Bool :=
  Function.update base output (remainingRows rowBlock n r ++ base output)

/-- A per-vertex body certificate must actually execute in the combined
program, preserve the remaining unary vertex counter and caller frame, and
prepend precisely that vertex's ordered block of rows. -/
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

/-- Derives the complete outer enumeration trace from the actual row-body
traces. Descending cursor order and prepending produce canonical ascending
vertex order on the output tape. The zero delimiter is retained for cleanup. -/
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

/-- The output field is exactly the completed canonical row stream. -/
theorem vertexLoop_output (counter output : K) (different : output ≠ counter)
    (base : K → List Bool) (suffix : List Bool) (rowBlock : Nat → List Bool) (n : Nat) :
    MachineUnaryCounter.counterTapes counter (rowBase output base rowBlock n 0) 0 suffix output =
      remainingRows rowBlock n 0 ++ base output := by
  simp [MachineUnaryCounter.counterTapes, rowBase, different]

/-- Lookup scan suffixes and other work tapes may evolve between vertices.
Only the output field is replaced by the prescribed canonical row suffix. -/
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

/-- The outer loop with a varying work-tape frame. Actual row-body traces
determine that frame; no cleanup of accumulated lookup suffixes is assumed. -/
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

end MaxCutGames.Foundations.Complexity.PoweringMachineLoop

end OAI
