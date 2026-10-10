import OAI.Computability.BinPacking.CookLevin.ProducerFrontStage
import OAI.Computability.BinPacking.CookLevin.TransitionIteration

namespace OAI

noncomputable section

namespace BinPackingGames.Foundations.Complexity.CookLevin.AcceptanceMachine

open Turing MachineComposition TermMachine TransitionTemplate PostfixModel

inductive RootLabel
  | seed | scan | restore
  | lookup (label : LookupLabel)
  deriving DecidableEq, Fintype

def widthAddress (coefficient offset : Nat) (input : Input) : Nat :=
  coefficient * input.capacity + offset

def rootProgram (coefficient offset : Nat) : RootLabel → TM2.Stmt Alphabet RootLabel State
  | .seed => MachineUnaryAffineAt.seed .address offset .scan
  | .scan => MachineUnaryAffineAt.scan .capacity .scratch .address coefficient .scan .restore
  | .restore => Reduction.MachineTransfer.loopAt .scratch .capacity id false .restore
      (some (.lookup (.lookup (.run .copyFirst))))
  | .lookup label => MachineSubroutine.statement RootLabel.lookup none (lookupProgram 0 label)

def rootSteps (coefficient offset : Nat) (input : Input) : Nat :=
  (2 * (input.capacity + 1) + 1) +
    (MachinePreservingLookupClean.steps input.roots (widthAddress coefficient offset input) +
      rootLookup input.roots (widthAddress coefficient offset input) + 4)

private theorem trace_trans {α : Type*} (f : α → α) {a b : Nat} {x y z : α}
    (first : f^[a] x = y) (second : f^[b] y = z) : f^[a + b] x = z := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

theorem rootTrace (coefficient offset : Nat) (input : Input)
    (present : input.roots[widthAddress coefficient offset input]? =
      some (rootLookup input.roots (widthAddress coefficient offset input)))
    (base : Tape → List Bool) (frame : Frame input base) :
    (advance (TM2.step (rootProgram coefficient offset)))^[rootSteps coefficient offset input]
      (some ⟨some .seed, initialState, base⟩) =
      some ⟨none, initialState, emitTapes base
        [.input (rootLookup input.roots (widthAddress coefficient offset input))]⟩ := by
  have ha := frame.clean .address (by rfl)
  have hs := frame.clean .scratch (by rfl)
  have affine := MachineUnaryAffineAt.seededAffineTrace .capacity .scratch .address
    (by decide) (by decide) (by decide) coefficient offset RootLabel.seed
    RootLabel.scan RootLabel.restore (some (.lookup (.lookup (.run .copyFirst))))
    (rootProgram coefficient offset) rfl rfl rfl base input.capacity []
    (by simpa using frame.capacityWord) hs ((), false) none
  simp only [ha, List.append_nil] at affine
  have source := lookupTailTrace 0 input (widthAddress coefficient offset input) present base frame
  have lookup := MachineSubroutine.trace RootLabel.lookup none (lookupProgram 0)
    (rootProgram coefficient offset) (fun _ => rfl)
    (MachinePreservingLookupClean.steps input.roots (widthAddress coefficient offset input) +
      rootLookup input.roots (widthAddress coefficient offset input) + 4) _ _ source
  simp only [MachineSubroutine.configuration, MachineSubroutine.label] at lookup
  exact trace_trans _ affine lookup

theorem rootSteps_le (coefficient offset : Nat) (input : Input)
    (present : input.roots[widthAddress coefficient offset input]? =
      some (rootLookup input.roots (widthAddress coefficient offset input))) :
    rootSteps coefficient offset input ≤ 12 * (input.size + 1) := by
  have hl := MachinePreservingLookupClean.steps_le input.roots
    (widthAddress coefficient offset input) _ present
  have hw := MachineLookupSpec.output_length_le input.roots
    (widthAddress coefficient offset input) _ present
  rw [encodeWord_length] at hw
  unfold rootSteps Input.size
  omega

def rootEmitter (valid : Input → Prop) (coefficient offset : Nat)
    (present : ∀ input, valid input →
      input.roots[widthAddress coefficient offset input]? =
        some (rootLookup input.roots (widthAddress coefficient offset input))) :
    Emitter valid (fun input =>
      [.input (rootLookup input.roots (widthAddress coefficient offset input))]) where
  Label := RootLabel
  finite := inferInstance
  entry := .seed
  program := rootProgram coefficient offset
  steps := rootSteps coefficient offset
  constant := 12
  trace input hv base frame := rootTrace coefficient offset input (present input hv) base frame
  bound input hv := rootSteps_le coefficient offset input (present input hv)

def closurePorts : OrClosure.Ports Tape :=
  ⟨.position, .reversed, .count, by decide, by decide, by decide⟩

inductive ClosureLabel
  | seed | scan | restore | orSeed | orLoop | finish
  deriving DecidableEq

protected abbrev ClosureLabel.enumList : List ClosureLabel := [.seed, .scan, .restore, .orSeed,
  .orLoop, .finish]

protected theorem ClosureLabel.enumList_getElem?_ctorIdx_eq (x : ClosureLabel) :
    ClosureLabel.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem ClosureLabel.enumList_nodup : ClosureLabel.enumList.Nodup := by decide

instance : Fintype ClosureLabel where
  elems := ⟨ClosureLabel.enumList, ClosureLabel.enumList_nodup⟩
  complete x := by cases x <;> decide

def closureProgram (coefficient offset : Nat) :
    ClosureLabel → TM2.Stmt Alphabet ClosureLabel State
  | .seed => MachineUnaryAffineAt.seed .position offset .scan
  | .scan => MachineUnaryAffineAt.scan .capacity .scratch .position coefficient .scan .restore
  | .restore => Reduction.MachineTransfer.loopAt .scratch .capacity id false .restore (some .orSeed)
  | .orSeed => OrClosure.seed closurePorts .orLoop
  | .orLoop => OrClosure.loop closurePorts .orLoop (some .finish)
  | .finish => .pop .position (fun _ _ => initialState) .halt

def closureSteps (coefficient offset : Nat) (input : Input) : Nat :=
  (2 * (input.capacity + 1) + 1) + (widthAddress coefficient offset input + 2) + 1

theorem closureTrace (coefficient offset : Nat) (input : Input)
    (base : Tape → List Bool) (frame : Frame input base) :
    (advance (TM2.step (closureProgram coefficient offset)))^[closureSteps coefficient offset input]
      (some ⟨some .seed, initialState, base⟩) =
      some ⟨none, initialState, emitTapes base
        (InitializationTemplate.closeOr (widthAddress coefficient offset input))⟩ := by
  let width := widthAddress coefficient offset input
  let finished := OrClosure.frame closurePorts base (encodeWord 0)
    ((tokenBits (InitializationTemplate.closeOr width)).reverse ++ base .reversed)
    (List.replicate (width + 1) true ++ base .count)
  have hp := frame.clean .position (by rfl)
  have hs := frame.clean .scratch (by rfl)
  have affine := MachineUnaryAffineAt.seededAffineTrace .capacity .scratch .position
    (by decide) (by decide) (by decide) coefficient offset ClosureLabel.seed
    ClosureLabel.scan ClosureLabel.restore (some .orSeed)
    (closureProgram coefficient offset) rfl rfl rfl base input.capacity []
    (by simpa using frame.capacityWord) hs ((), false) none
  simp only [hp, List.append_nil] at affine
  have closure := OrClosure.closureTrace closurePorts ClosureLabel.orSeed ClosureLabel.orLoop
    (some .finish) (closureProgram coefficient offset) rfl rfl base width []
    (base .reversed) (base .count) ((), false) none
  have startFrame : OrClosure.frame closurePorts base (encodeWord width ++ [])
      (base .reversed) (base .count) = Function.update base .position (encodeWord width) := by
    funext tape
    cases tape <;> simp [OrClosure.frame, closurePorts]
  rw [startFrame] at closure
  simp only [List.append_nil] at closure
  have finish : (advance (TM2.step (closureProgram coefficient offset)))^[1]
      (some ⟨some .finish, initialState, finished⟩) =
      some ⟨none, initialState, emitTapes base (InitializationTemplate.closeOr width)⟩ := by
    change some (TM2.stepAux (closureProgram coefficient offset .finish) initialState finished) = _
    simp only [closureProgram, TM2.stepAux]
    congr 2
    funext tape
    cases tape <;> simp [finished, OrClosure.frame, closurePorts, emitTapes,
      InitializationTemplate.closeOr, encodeWord, hp, Nat.add_comm]
  exact trace_trans _ (trace_trans _ affine closure) finish

theorem closureSteps_le (coefficient offset : Nat) (input : Input) :
    closureSteps coefficient offset input ≤ (coefficient + offset + 8) * (input.size + 1) := by
  have hs : input.capacity ≤ input.size := by simp [Input.size]; omega
  have hmul := Nat.mul_le_mul_left coefficient hs
  unfold closureSteps widthAddress
  nlinarith

def closureEmitter (valid : Input → Prop) (coefficient offset : Nat) :
    Emitter valid (fun input => InitializationTemplate.closeOr (widthAddress coefficient offset input)) where
  Label := ClosureLabel
  finite := inferInstance
  entry := .seed
  program := closureProgram coefficient offset
  steps := closureSteps coefficient offset
  constant := coefficient + offset + 8
  trace input _ base frame := closureTrace coefficient offset input base frame
  bound input _ := closureSteps_le coefficient offset input

section Indexed

variable {K Λ σ : Type} {Γ : K → Type}

def Valid (indexing : ConfigIndex.Indexing Γ Λ σ) (input : Input) : Prop :=
  indexing.width input.capacity < input.roots.length

theorem Valid.roots {indexing : ConfigIndex.Indexing Γ Λ σ} {input : Input}
    (valid : Valid indexing input) : RootsValid indexing input := Nat.le_of_lt valid

theorem Valid.transition {indexing : ConfigIndex.Indexing Γ Λ σ} {input : Input}
    (valid : Valid indexing input) (plan : TransitionMachine.Plan (Γ := Γ) (Λ := Λ) (σ := σ)) :
    TransitionMachine.Valid indexing plan input := by
  unfold Valid at valid
  unfold TransitionMachine.Valid
  cases plan.carry <;> simp only [Bool.false_eq_true, ite_true, ite_false] <;> omega

theorem Valid.withCursor {indexing : ConfigIndex.Indexing Γ Λ σ} {input : Input}
    (valid : Valid indexing input) (cursor : Nat) :
    Valid indexing (TransitionMachine.withCursor input cursor) := valid

theorem widthAddress_eq (indexing : ConfigIndex.Indexing Γ Λ σ) (input : Input) :
    widthAddress indexing.symbolCount (indexing.labelCount + indexing.stateCount) input =
      indexing.width input.capacity := by
  simp [widthAddress, ConfigIndex.Indexing.width, Nat.mul_comm,
    Nat.add_comm, Nat.add_assoc]

def carryTokens (indexing : ConfigIndex.Indexing Γ Λ σ) (input : Input) : List Token :=
  [.input (rootLookup input.roots (indexing.width input.capacity))]

variable [DecidableEq K] [Fintype σ] [DecidableEq σ]
variable [∀ k, DecidableEq (Γ k)] [∀ k, Fintype (Γ k)] [DecidableEq Λ] [Fintype Λ]

def carryEmitter (indexing : ConfigIndex.Indexing Γ Λ σ) :
    Emitter (Valid indexing) (carryTokens indexing) :=
  (rootEmitter (Valid indexing) indexing.symbolCount (indexing.labelCount + indexing.stateCount)
    (fun input hv => by
      rw [widthAddress_eq]
      simp only [rootLookup, List.getElem?_eq_getElem hv, Option.getD_some])).congr
        (fun input => by rw [widthAddress_eq]; rfl)

def orEmitter (indexing : ConfigIndex.Indexing Γ Λ σ) :
    Emitter (Valid indexing) (fun input => InitializationTemplate.closeOr (indexing.width input.capacity)) :=
  (closureEmitter (Valid indexing) indexing.symbolCount (indexing.labelCount + indexing.stateCount)).congr
    (fun input => by rw [widthAddress_eq])

def finishEmitter (indexing : ConfigIndex.Indexing Γ Λ σ) :
    Emitter (Valid indexing) (fun _ => [.not, .and]) :=
  Emitter.literal (Valid indexing) [.not, .and]

inductive Label (indexing : ConfigIndex.Indexing Γ Λ σ)
    (plan : TransitionMachine.Plan (Γ := Γ) (Λ := Λ) (σ := σ))
  | carry (label : (carryEmitter indexing).Label)
  | mismatch (label : TransitionMachine.Label indexing plan)
  | close (label : (orEmitter indexing).Label)
  | finish (label : (finishEmitter indexing).Label)
  deriving Fintype

attribute [-instance] instFintypeLabel

instance labelFintype (indexing : ConfigIndex.Indexing Γ Λ σ)
    (plan : TransitionMachine.Plan (Γ := Γ) (Λ := Λ) (σ := σ)) : Fintype (Label indexing plan) :=
  Fintype.ofEquiv
    ((carryEmitter indexing).Label ⊕ TransitionMachine.Label indexing plan ⊕
      (orEmitter indexing).Label ⊕ (finishEmitter indexing).Label)
    (Label.proxyTypeEquiv indexing plan)

def program (indexing : ConfigIndex.Indexing Γ Λ σ)
    (plan : TransitionMachine.Plan (Γ := Γ) (Λ := Λ) (σ := σ)) :
    Label indexing plan → TM2.Stmt Alphabet (Label indexing plan) State
  | .carry label => MachineSubroutine.statement Label.carry
      (some (.mismatch (.prefix (TransitionMachine.compilePrefix indexing plan.prefix).entry)))
      ((carryEmitter indexing).program label)
  | .mismatch label => MachineSubroutine.statement Label.mismatch
      (some (.close (orEmitter indexing).entry)) (TransitionMachine.program indexing plan label)
  | .close label => MachineSubroutine.statement Label.close
      (some (.finish (finishEmitter indexing).entry)) ((orEmitter indexing).program label)
  | .finish label => MachineSubroutine.statement Label.finish none ((finishEmitter indexing).program label)

def machine (indexing : ConfigIndex.Indexing Γ Λ σ)
    (plan : TransitionMachine.Plan (Γ := Γ) (Λ := Λ) (σ := σ)) : FinTM2 where
  K := Tape
  k₀ := .capacity
  k₁ := .reversed
  Γ := Alphabet
  Λ := Label indexing plan
  main := .carry (carryEmitter indexing).entry
  σ := State
  initialState := initialState
  m := program indexing plan

def outputTokens (indexing : ConfigIndex.Indexing Γ Λ σ)
    (plan : TransitionMachine.Plan (Γ := Γ) (Λ := Λ) (σ := σ)) (input : Input) : List Token :=
  carryTokens indexing input ++ TransitionMachine.outputTokens indexing plan input ++
    InitializationTemplate.closeOr (indexing.width input.capacity) ++ [.not, .and]

def steps (indexing : ConfigIndex.Indexing Γ Λ σ)
    (plan : TransitionMachine.Plan (Γ := Γ) (Λ := Λ) (σ := σ)) (input : Input) : Nat :=
  (carryEmitter indexing).steps (TransitionMachine.withCursor input 0) +
    TransitionMachine.steps indexing plan input +
    (orEmitter indexing).steps (TransitionMachine.withCursor input 0) + 1

omit [DecidableEq K] [Fintype σ] [DecidableEq σ]
  [(tape : K) → DecidableEq (Γ tape)] [(tape : K) → Fintype (Γ tape)]
  [DecidableEq Λ] [Fintype Λ] in
theorem fullTrace (indexing : ConfigIndex.Indexing Γ Λ σ)
    (plan : TransitionMachine.Plan (Γ := Γ) (Λ := Λ) (σ := σ)) (input : Input)
    (valid : Valid indexing input) (base : Tape → List Bool)
    (frame : Frame (TransitionMachine.withCursor input 0) base) :
    (advance (TM2.step (program indexing plan)))^[steps indexing plan input]
      (some ⟨some (Label.carry (carryEmitter indexing).entry), initialState, base⟩) =
      some ⟨none, initialState, emitTapes base (outputTokens indexing plan input)⟩ := by
  let carried := emitTapes base (carryTokens indexing input)
  let mismatch := emitTapes carried (TransitionMachine.outputTokens indexing plan input)
  let closed := emitTapes mismatch (InitializationTemplate.closeOr (indexing.width input.capacity))
  have carry := (carryEmitter indexing).traceAt Label.carry
    (some (.mismatch (.prefix (TransitionMachine.compilePrefix indexing plan.prefix).entry)))
    (program indexing plan) (fun _ => rfl) (TransitionMachine.withCursor input 0)
    (valid.withCursor 0) base frame
  have hcarry : Frame (TransitionMachine.withCursor input 0) carried :=
    frame.emit (carryTokens indexing input)
  have mid := TransitionMachine.traceAt indexing plan Label.mismatch
    (some (.close (orEmitter indexing).entry)) (program indexing plan) (fun _ => rfl)
    input (valid.transition plan) carried hcarry
  have hmid := hcarry.emit (TransitionMachine.outputTokens indexing plan input)
  have close := (orEmitter indexing).traceAt Label.close
    (some (.finish (finishEmitter indexing).entry)) (program indexing plan) (fun _ => rfl)
    (TransitionMachine.withCursor input 0) (valid.withCursor 0) mismatch hmid
  have hclose := hmid.emit (InitializationTemplate.closeOr (indexing.width input.capacity))
  have finish := (finishEmitter indexing).traceAt Label.finish none
    (program indexing plan) (fun _ => rfl) (TransitionMachine.withCursor input 0)
    (valid.withCursor 0) closed hclose
  have h := trace_trans _ (trace_trans _ (trace_trans _ carry mid) close) finish
  simpa only [steps, carried, mismatch, closed, finishEmitter, Emitter.literal,
    TransitionMachine.withCursor_capacity, TransitionMachine.withCursor_roots,
    carryTokens, emitTapes_append, outputTokens, List.append_assoc] using h

def timeConstant (indexing : ConfigIndex.Indexing Γ Λ σ)
    (plan : TransitionMachine.Plan (Γ := Γ) (Λ := Λ) (σ := σ)) : Nat :=
  (carryEmitter indexing).constant + TransitionMachine.timeConstant indexing plan +
    (orEmitter indexing).constant + 1

noncomputable def timePolynomial (indexing : ConfigIndex.Indexing Γ Λ σ)
    (plan : TransitionMachine.Plan (Γ := Γ) (Λ := Λ) (σ := σ)) : Polynomial Nat :=
  Polynomial.C (timeConstant indexing plan) * (Polynomial.X + 1)^2

omit [DecidableEq K] [Fintype σ] [DecidableEq σ]
  [(tape : K) → DecidableEq (Γ tape)] [(tape : K) → Fintype (Γ tape)]
  [DecidableEq Λ] [Fintype Λ] in
theorem steps_le (indexing : ConfigIndex.Indexing Γ Λ σ)
    (plan : TransitionMachine.Plan (Γ := Γ) (Λ := Λ) (σ := σ)) (input : Input)
    (valid : Valid indexing input) :
    steps indexing plan input ≤ timeConstant indexing plan * (TransitionMachine.dataSize input + 1)^2 := by
  have hc := (carryEmitter indexing).bound (TransitionMachine.withCursor input 0) (valid.withCursor 0)
  have hm := TransitionMachine.steps_le indexing plan input (valid.transition plan)
  have ho := (orEmitter indexing).bound (TransitionMachine.withCursor input 0) (valid.withCursor 0)
  have hs : (TransitionMachine.withCursor input 0).size = TransitionMachine.dataSize input := by
    simp [TransitionMachine.withCursor, Input.size, TransitionMachine.dataSize]
  rw [hs] at hc ho
  have hsq : TransitionMachine.dataSize input + 1 ≤ (TransitionMachine.dataSize input + 1)^2 := by
    nlinarith
  have hc' := hc.trans (Nat.mul_le_mul_left (carryEmitter indexing).constant hsq)
  have ho' := ho.trans (Nat.mul_le_mul_left (orEmitter indexing).constant hsq)
  unfold steps timeConstant
  nlinarith

def inPolynomialTime (indexing : ConfigIndex.Indexing Γ Λ σ)
    (plan : TransitionMachine.Plan (Γ := Γ) (Λ := Λ) (σ := σ)) (input : Input)
    (valid : Valid indexing input) (base : Tape → List Bool)
    (frame : Frame (TransitionMachine.withCursor input 0) base) :
    StateTransition.EvalsToInTime (machine indexing plan).step
      ⟨some (Label.carry (carryEmitter indexing).entry), initialState, base⟩
      (some ⟨none, initialState, emitTapes base (outputTokens indexing plan input)⟩)
      ((timePolynomial indexing plan).eval (TransitionMachine.dataSize input)) where
  steps := steps indexing plan input
  evals_in_steps := fullTrace indexing plan input valid base frame
  steps_le_m := by
    simpa only [timePolynomial, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one] using steps_le indexing plan input valid

end Indexed

open VerifierCircuit AcceptanceTemplate

local instance iterationTimeVerifierLabelFintype (V : NPVerifier) : Fintype V.computation.tm.Λ := V.computation.tm.ΛFin
local instance iterationTimeVerifierStateFintype (V : NPVerifier) : Fintype V.computation.tm.σ := V.computation.tm.σFin
local instance iterationTimeVerifierAlphabetFintype (V : NPVerifier) : ∀ k, Fintype (V.computation.tm.Γ k) := V.finiteAlphabet
local instance iterationTimeVerifierLabelDecidableEq (V : NPVerifier) : DecidableEq V.computation.tm.Λ := Classical.decEq _
local instance iterationTimeVerifierStateDecidableEq (V : NPVerifier) : DecidableEq V.computation.tm.σ := Classical.decEq _
local instance iterationTimeVerifierAlphabetDecidableEq (V : NPVerifier) : ∀ k, DecidableEq (V.computation.tm.Γ k) :=
  fun _ => Classical.decEq _

theorem rootLookup_ofFn {n : Nat} (wire : Fin n → Nat) (i : Fin n) :
    rootLookup (List.ofFn wire) i.val = wire i := by
  simp [rootLookup, i.isLt]

theorem mismatchForest_ofFn (V : NPVerifier) (input : List Bool)
    (wire : Fin (width V input + 1) → Nat) :
    AcceptancePlan.mismatchForest V (List.ofFn wire) (capacity V input.length) =
      (List.ofFn fun j : Fin (width V input) =>
        mismatchTokens (targetBit V input j) (wire j.castSucc)).flatten := by
  rw [AcceptancePlan.mismatchForest_circuit]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext j
  exact congrArg (mismatchTokens (targetBit V input j)) (rootLookup_ofFn wire j.castSucc)

def verifierInput (V : NPVerifier) (input : List Bool)
    (wire : Fin (width V input + 1) → Nat) : Input :=
  ⟨0, capacity V input.length, List.ofFn wire⟩

theorem verifierInput_valid (V : NPVerifier) (input : List Bool)
    (wire : Fin (width V input + 1) → Nat) :
    Valid (indexing V) (verifierInput V input wire) := by
  simp [Valid, verifierInput, width]

theorem outputTokens_eq_acceptance (V : NPVerifier) (input : List Bool)
    (wire : Fin (width V input + 1) → Nat) :
    outputTokens (indexing V) (AcceptancePlan.plan V) (verifierInput V input wire) =
      AcceptanceTemplate.tokens V input wire := by
  have hw : (fun j : Fin (width V input + 1) => rootLookup (List.ofFn wire) j.val) = wire :=
    funext (rootLookup_ofFn wire)
  have h := (AcceptancePlan.fullTokens_eq V input (List.ofFn wire)).symm
  rw [hw] at h
  simpa only [outputTokens, carryTokens, verifierInput, width] using h

theorem compile_outputTokens (V : NPVerifier) (input : List Bool)
    (wire : Fin (width V input + 1) → Nat) (start : Nat) (oldRoots : List Nat) :
    compileTokens start oldRoots
      (outputTokens (indexing V) (AcceptancePlan.plan V) (verifierInput V input wire)) =
      some (start + (acceptanceExpr V input).size,
        (acceptanceExpr V input).root start :: oldRoots,
        (acceptanceExpr V input).gates wire start) := by
  rw [outputTokens_eq_acceptance]
  exact AcceptanceTemplate.compile_tokens V input wire start oldRoots

theorem outputTokens_length_le (V : NPVerifier) (input : List Bool)
    (wire : Fin (width V input + 1) → Nat) :
    (outputTokens (indexing V) (AcceptancePlan.plan V) (verifierInput V input wire)).length ≤
      3 * width V input + 4 := by
  rw [outputTokens_eq_acceptance]
  exact AcceptanceTemplate.tokens_length_le V input wire

def verifierMachine (V : NPVerifier) : FinTM2 :=
  machine (indexing V) (AcceptancePlan.plan V)

def verifierInPolynomialTime (V : NPVerifier) (input : List Bool)
    (wire : Fin (width V input + 1) → Nat) (base : Tape → List Bool)
    (frame : Frame (verifierInput V input wire) base) :
    StateTransition.EvalsToInTime (verifierMachine V).step
      ⟨some (Label.carry (carryEmitter (indexing V)).entry), initialState, base⟩
      (some ⟨none, initialState, emitTapes base (AcceptanceTemplate.tokens V input wire)⟩)
      ((timePolynomial (indexing V) (AcceptancePlan.plan V)).eval
        (TransitionMachine.dataSize (verifierInput V input wire))) := by
  have run := inPolynomialTime (indexing V) (AcceptancePlan.plan V) (verifierInput V input wire)
    (verifierInput_valid V input wire) base frame
  rw [outputTokens_eq_acceptance] at run
  exact run

end BinPackingGames.Foundations.Complexity.CookLevin.AcceptanceMachine

namespace BinPackingGames.Foundations.Complexity.CookLevin.AcceptanceStage

open Turing MachineComposition StatementCircuit CircuitBatch
open PostfixModel PostfixAlignment ProducerInvariant VerifierCircuit
open TransitionArena

local instance iterationTimeVerifierLabelFintype (V : NPVerifier) : Fintype V.computation.tm.Λ := V.computation.tm.ΛFin
local instance iterationTimeVerifierStateFintype (V : NPVerifier) : Fintype V.computation.tm.σ := V.computation.tm.σFin
local instance iterationTimeVerifierAlphabetFintype (V : NPVerifier) : ∀ k, Fintype (V.computation.tm.Γ k) := V.finiteAlphabet
local instance iterationTimeVerifierLabelDecidableEq (V : NPVerifier) : DecidableEq V.computation.tm.Λ := Classical.decEq _
local instance iterationTimeVerifierStateDecidableEq (V : NPVerifier) : DecidableEq V.computation.tm.σ := Classical.decEq _
local instance iterationTimeVerifierAlphabetDecidableEq (V : NPVerifier) : ∀ k, DecidableEq (V.computation.tm.Γ k) :=
  fun _ => Classical.decEq _

abbrev EmitLabel (V : NPVerifier) :=
  AcceptanceMachine.Label (indexing V) (AcceptancePlan.plan V)

abbrev Label (V : NPVerifier) := EmitLabel V ⊕ ForestStage.Label

def entry (V : NPVerifier) : Label V :=
  .inl (.carry (AcceptanceMachine.carryEmitter (indexing V)).entry)

def program (V : NPVerifier) : Label V → TM2.Stmt Alphabet (Label V) State
  | .inl label => ForestPlacement.statement termPorts Sum.inl
      (some (.inr .reverseTokens))
      (AcceptanceMachine.program (indexing V) (AcceptancePlan.plan V) label)
  | .inr label => ForestStage.statement forestPorts Sum.inr none label

def machine (V : NPVerifier) : FinTM2 where
  K := Tape
  k₀ := .inr .capacity
  k₁ := .inl .records
  Γ := Alphabet
  Λ := Label V
  main := entry V
  σ := State
  initialState := TermMachine.initialState
  m := program V

def expressions (V : NPVerifier) (input : List Bool) :
    Fin 1 → Expr (Fin (width V input + 1)) :=
  fun _ => acceptanceExpr V input

def wireValues {inputs count : Nat} (frame : Frame inputs count) : Fin count → Nat :=
  fun i => (frame.wires i).val

theorem tokens_eq_forest (V : NPVerifier) (input : List Bool)
    (wire : Fin (width V input + 1) → Nat) :
    AcceptanceTemplate.tokens V input wire =
      forestTokens wire (List.ofFn (expressions V input)) := by
  rw [AcceptanceTemplate.tokens_eq]
  simp [expressions, List.ofFn_succ, forestTokens]

theorem finish_termFrame (base : Tape → List Bool) (S : Nat) (s : Snapshot) :
    TermMachine.Frame (termInput S s)
      (fun tape => finishTapes base S s (termPorts tape)) := by
  have restriction : (fun tape => finishTapes base S s (termPorts tape)) =
      (fun tape => tapes base S 0 s (termPorts tape)) := by
    simp only [termPorts]
    funext tape
    change Function.update (tapes base S 0 s) (Sum.inr Extra.countdown) [] (termTape tape) =
      tapes base S 0 s (termTape tape)
    cases tape <;> simp [termTape]
  rw [restriction]
  exact termFrame base S 0 s

def prepared (base : Tape → List Bool) (S : Nat) (s : Snapshot)
    (tokens : List Token) : Tape → List Bool :=
  Function.update
    (Function.update (finishTapes base S s) (.inl .tokens) (tokenBits tokens).reverse)
    (.inl (.lower .remaining)) (encodeWord tokens.length)

theorem finish_place_emitTapes (base : Tape → List Bool) (S : Nat) (s : Snapshot)
    (tokens : List Token) :
    ForestPlacement.fill termPorts (finishTapes base S s)
      (TermMachine.emitTapes (fun tape => finishTapes base S s (termPorts tape)) tokens) =
      prepared base S s tokens := by
  simp only [TermMachine.emitTapes, ForestPlacement.fill_update, ForestPlacement.fill_self]
  simp [termTape, tapes, finishTapes, prepared, encodeWord]

theorem prepared_eq_lower (base : Tape → List Bool) (S : Nat) (s : Snapshot)
    (tokens : List Token) :
    prepared base S s tokens =
      ForestPlacement.fill forestPorts (finishTapes base S s)
        (ForestStage.initialLocal s.current tokens s.reversedRecords (encodeWords s.roots)) := by
  rw [fill_forest]
  funext tape
  cases tape with
  | inl tape =>
    cases tape with
    | lower tape => cases tape <;>
        simp [prepared, finishTapes, tapes, ForestStage.initialLocal]
    | tokens => simp [prepared, finishTapes, ForestStage.initialLocal]
    | records => simp [prepared, finishTapes, tapes, ForestStage.initialLocal]
    | rootTable => simp [prepared, finishTapes, tapes, ForestStage.initialLocal]
  | inr tape => cases tape <;>
      simp [prepared, finishTapes, tapes]

theorem lower_final_eq {inputs oldWidth newWidth : Nat}
    (base : Tape → List Bool) (S : Nat) (frame : Frame inputs oldWidth)
    (es : Fin newWidth → Expr (Fin oldWidth)) :
    ForestPlacement.fill forestPorts (finishTapes base S (snapshot frame))
      (ForestStage.finalLocal (next (frame.step es)) (rootValues (frame.step es)).reverse
        (recordsBits (gateRecords (next frame)
          (Batch.gates (wireValues frame) (next frame) (List.ofFn es))))
        (recordBits frame).reverse) =
      finishTapes base S (snapshot (frame.step es)) := by
  rw [fill_forest]
  funext tape
  cases tape with
  | inl tape =>
    cases tape with
    | lower tape => cases tape <;> rfl
    | tokens => rfl
    | records =>
      change (recordsBits (gateRecords (next frame)
        (Batch.gates (wireValues frame) (next frame) (List.ofFn es)))).reverse ++
        (recordBits frame).reverse = (recordBits (frame.step es)).reverse
      rw [recordBits_step, List.reverse_append]
      rfl
    | rootTable =>
      change encodeWords (rootValues (frame.step es)).reverse.reverse =
        encodeWords (rootValues (frame.step es))
      rw [List.reverse_reverse]
  | inr tape => cases tape <;> rfl

def emissionSteps (V : NPVerifier) (input : List Bool) {inputs : Nat}
    (frame : Frame inputs (width V input + 1)) : Nat :=
  AcceptanceMachine.steps (indexing V) (AcceptancePlan.plan V)
    (AcceptanceMachine.verifierInput V input (wireValues frame))

def loweringSteps (V : NPVerifier) (input : List Bool) {inputs : Nat}
    (frame : Frame inputs (width V input + 1)) : Nat :=
  ForestStage.steps (AcceptanceTemplate.tokens V input (wireValues frame)) (next frame)
    (rootValues (frame.step (expressions V input))).reverse
    (Batch.gates (wireValues frame) (next frame) (List.ofFn (expressions V input)))
    (encodeWords (rootValues frame))

def steps (V : NPVerifier) (input : List Bool) {inputs : Nat}
    (frame : Frame inputs (width V input + 1)) : Nat :=
  emissionSteps V input frame + loweringSteps V input frame

private theorem chain {α : Type*} (f : α → α) {n m : Nat} {a b c : α}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm n m, Function.iterate_add_apply, first, second]

theorem fullTrace (V : NPVerifier) (input : List Bool) {inputs : Nat}
    (frame : Frame inputs (width V input + 1)) (base : Tape → List Bool) :
    (advance (TM2.step (program V)))^[steps V input frame]
      (some ⟨some (entry V), TermMachine.initialState,
        finishTapes base (capacity V input.length) (snapshot frame)⟩) =
      some ⟨none, TermMachine.initialState,
        finishTapes base (capacity V input.length)
          (snapshot (frame.step (expressions V input)))⟩ := by
  let boundary := finishTapes base (capacity V input.length) (snapshot frame)
  let wire := wireValues frame
  let inp := AcceptanceMachine.verifierInput V input wire
  let tokens := AcceptanceTemplate.tokens V input wire
  have hframe : TermMachine.Frame inp (fun tape => boundary (termPorts tape)) :=
    finish_termFrame base (capacity V input.length) (snapshot frame)
  have source := AcceptanceMachine.fullTrace (indexing V) (AcceptancePlan.plan V) inp
    (AcceptanceMachine.verifierInput_valid V input wire)
    (fun tape => boundary (termPorts tape)) hframe
  rw [AcceptanceMachine.outputTokens_eq_acceptance] at source
  have emitter := ForestPlacement.trace termPorts Sum.inl (some (.inr .reverseTokens))
    boundary (AcceptanceMachine.program (indexing V) (AcceptancePlan.plan V))
    (program V) (fun _ => rfl) _ _ _ source
  change (advance (TM2.step (program V)))^[emissionSteps V input frame]
    (some ⟨some (entry V), TermMachine.initialState,
      ForestPlacement.fill termPorts boundary (fun tape => boundary (termPorts tape))⟩) =
      some ⟨some (.inr .reverseTokens), TermMachine.initialState,
        ForestPlacement.fill termPorts boundary
          (TermMachine.emitTapes (fun tape => boundary (termPorts tape)) tokens)⟩ at emitter
  rw [ForestPlacement.fill_self] at emitter
  rw [finish_place_emitTapes, prepared_eq_lower] at emitter
  have valid := compile_frameForest frame (expressions V input)
  rw [← tokens_eq_forest] at valid
  have lower := ForestStage.traceAt forestPorts Sum.inr none (program V) (fun _ => rfl)
    boundary ((), false) tokens (next frame) (next (frame.step (expressions V input)))
    (rootValues (frame.step (expressions V input))).reverse
    (Batch.gates wire (next frame) (List.ofFn (expressions V input)))
    (recordBits frame).reverse (encodeWords (rootValues frame)) valid
  rw [lower_final_eq] at lower
  exact chain _ emitter lower

def budget (V : NPVerifier) (input : List Bool) {inputs : Nat}
    (frame : Frame inputs (width V input + 1)) : Nat :=
  (AcceptanceMachine.timePolynomial (indexing V) (AcceptancePlan.plan V)).eval
      (TransitionMachine.dataSize
        (AcceptanceMachine.verifierInput V input (wireValues frame))) +
    ForestStage.timePolynomial.eval
      (next frame + Batch.cost (List.ofFn (expressions V input)) +
        (tokenBits (AcceptanceTemplate.tokens V input (wireValues frame))).length +
        (encodeWords (rootValues frame)).length + 1)

theorem steps_le_budget (V : NPVerifier) (input : List Bool) {inputs : Nat}
    (frame : Frame inputs (width V input + 1)) : steps V input frame ≤ budget V input frame := by
  have he := AcceptanceMachine.steps_le (indexing V) (AcceptancePlan.plan V)
    (AcceptanceMachine.verifierInput V input (wireValues frame))
    (AcceptanceMachine.verifierInput_valid V input (wireValues frame))
  have hl := ForestStage.forest_steps_le (wireValues frame) (List.ofFn (expressions V input))
    (next frame) (encodeWords (rootValues frame)) (fun i => (frame.wires i).isLt)
  have roots : rootValues (frame.step (expressions V input)) =
      Batch.roots (next frame) (List.ofFn (expressions V input)) :=
    step_roots frame (expressions V input)
  rw [← tokens_eq_forest] at hl
  unfold steps emissionSteps loweringSteps budget
  rw [roots]
  apply Nat.add_le_add _ hl
  simpa only [AcceptanceMachine.timePolynomial, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one] using he

def inTime (V : NPVerifier) (input : List Bool) {inputs : Nat}
    (frame : Frame inputs (width V input + 1)) (base : Tape → List Bool) :
    StateTransition.EvalsToInTime (machine V).step
      ⟨some (entry V), TermMachine.initialState,
        finishTapes base (capacity V input.length) (snapshot frame)⟩
      (some ⟨none, TermMachine.initialState,
        finishTapes base (capacity V input.length)
          (snapshot (frame.step (expressions V input)))⟩)
      (budget V input frame) where
  steps := steps V input frame
  evals_in_steps := fullTrace V input frame base
  steps_le_m := steps_le_budget V input frame

theorem verifierTrace (V : NPVerifier) (input : List Bool) (base : Tape → List Bool) :
    (advance (TM2.step (program V)))^[
      steps V input (timeFrame V input (V.horizon input.length))]
      (some ⟨some (entry V), TermMachine.initialState,
        finishTapes base (capacity V input.length)
          (snapshot (timeFrame V input (V.horizon input.length)))⟩) =
      some ⟨none, TermMachine.initialState,
        finishTapes base (capacity V input.length) (snapshot (finalFrame V input))⟩ :=
  fullTrace V input (timeFrame V input (V.horizon input.length)) base

theorem final_root_singleton (V : NPVerifier) (input : List Bool) (base : Tape → List Bool) :
    finishTapes base (capacity V input.length) (snapshot (finalFrame V input))
      (.inl .rootTable) = encodeWords [((finalFrame V input).wires 0).val] := by
  simp [finishTapes, tapes, snapshot, List.ofFn_succ]

end BinPackingGames.Foundations.Complexity.CookLevin.AcceptanceStage

namespace BinPackingGames.Foundations.Complexity.CookLevin.ProducerTime

open CircuitBatch StatementCircuit PostfixModel PostfixAlignment ProducerInvariant
open MachineComposition VerifierCircuit
open scoped BigOperators

local instance iterationTimeVerifierLabelFintype (V : NPVerifier) : Fintype V.computation.tm.Λ := V.computation.tm.ΛFin
local instance iterationTimeVerifierStateFintype (V : NPVerifier) : Fintype V.computation.tm.σ := V.computation.tm.σFin
local instance iterationTimeVerifierAlphabetFintype (V : NPVerifier) : ∀ k, Fintype (V.computation.tm.Γ k) := V.finiteAlphabet
local instance iterationTimeVerifierLabelDecidableEq (V : NPVerifier) : DecidableEq V.computation.tm.Λ := Classical.decEq _
local instance iterationTimeVerifierStateDecidableEq (V : NPVerifier) : DecidableEq V.computation.tm.σ := Classical.decEq _
local instance iterationTimeVerifierAlphabetDecidableEq (V : NPVerifier) : ∀ k, DecidableEq (V.computation.tm.Γ k) :=
  fun _ => Classical.decEq _

def bootstrapPolynomial (V : NPVerifier) : Polynomial Nat :=
  2 * WitnessEncoding.freeInputPolynomial V.witnessBound + 5

def validityPolynomial (V : NPVerifier) : Polynomial Nat :=
  ValidityMachine.Full.timePolynomial.comp V.witnessBound

def loweringPolynomial (V : NPVerifier) : Polynomial Nat :=
  ForestStage.timePolynomial.comp (4 * stageEnvelopePolynomial V + 1)

def transitionEmissionPolynomial (V : NPVerifier) : Polynomial Nat :=
  (TransitionMachine.timePolynomial (indexing V)
    (TransitionMachine.transitionPlan (indexing V) V.computation.tm.m)).comp
      (2 * stageEnvelopePolynomial V)

def acceptanceEmissionPolynomial (V : NPVerifier) : Polynomial Nat :=
  (AcceptanceMachine.timePolynomial (indexing V) (AcceptancePlan.plan V)).comp
    (2 * stageEnvelopePolynomial V)

def finishPolynomial (V : NPVerifier) : Polynomial Nat :=
  9 * budgetPolynomial V + tapePolynomial V + 18

def iterationPolynomial (V : NPVerifier) : Polynomial Nat :=
  Bounds.horizonPolynomial V.computation.time V.witnessBound *
    (1 + transitionEmissionPolynomial V + loweringPolynomial V) + 1

def knownPhasePolynomial (V : NPVerifier) : Polynomial Nat :=
  VerifierFront.timePolynomial V + bootstrapPolynomial V + 1 + validityPolynomial V +
    loweringPolynomial V + iterationPolynomial V + acceptanceEmissionPolynomial V +
    loweringPolynomial V + finishPolynomial V

def producerPolynomial (V : NPVerifier) (cellTime : Polynomial Nat) : Polynomial Nat :=
  knownPhasePolynomial V + cellTime

theorem bootstrapPolynomial_eval (V : NPVerifier) (n : Nat) :
    (bootstrapPolynomial V).eval n = 2 * (2 * V.witnessBound.eval n + 1) + 5 := by
  simp [bootstrapPolynomial]

theorem validity_steps_le (V : NPVerifier) (n : Nat) :
    ValidityMachine.Full.steps (V.witnessBound.eval n) ≤ (validityPolynomial V).eval n := by
  simpa only [validityPolynomial, Polynomial.eval_comp] using
    ValidityMachine.Full.steps_le_time (V.witnessBound.eval n)

theorem front_steps_le (V : NPVerifier) (input : List Bool) :
    (VerifierFront.prepareInTime V input ()).steps ≤
      (VerifierFront.timePolynomial V).eval input.length :=
  (VerifierFront.prepareInTime V input ()).steps_le_m

theorem loweringPolynomial_eval (V : NPVerifier) (n : Nat) :
    (loweringPolynomial V).eval n =
      25 * (4 * (stageEnvelopePolynomial V).eval n + 1)^2 +
      80 * (4 * (stageEnvelopePolynomial V).eval n + 1) + 20 := by
  simp [loweringPolynomial, ForestStage.timePolynomial]

theorem transitionEmissionPolynomial_eval (V : NPVerifier) (n : Nat) :
    (transitionEmissionPolynomial V).eval n =
      TransitionMachine.timeConstant (indexing V)
        (TransitionMachine.transitionPlan (indexing V) V.computation.tm.m) *
          (2 * (stageEnvelopePolynomial V).eval n + 1)^2 := by
  simp [transitionEmissionPolynomial, TransitionMachine.timePolynomial]

theorem acceptanceEmissionPolynomial_eval (V : NPVerifier) (n : Nat) :
    (acceptanceEmissionPolynomial V).eval n =
      AcceptanceMachine.timeConstant (indexing V) (AcceptancePlan.plan V) *
        (2 * (stageEnvelopePolynomial V).eval n + 1)^2 := by
  simp [acceptanceEmissionPolynomial, AcceptanceMachine.timePolynomial]

variable {inputs oldWidth newWidth : Nat}

def forestSteps (f : Frame inputs oldWidth) (es : Fin newWidth → Expr (Fin oldWidth))
    (oldRoots : List Bool) : Nat :=
  ForestStage.steps (forestTokens (fun i => (f.wires i).val) (List.ofFn es))
    (next f) (Batch.roots (next f) (List.ofFn es)).reverse
    (Batch.gates (fun i => (f.wires i).val) (next f) (List.ofFn es)) oldRoots

theorem forestSteps_le (V : NPVerifier) (input : List Bool)
    (f : Frame inputs oldWidth) (es : Fin newWidth → Expr (Fin oldWidth))
    (oldRoots : List Bool)
    (hc : next f ≤ (stageEnvelopePolynomial V).eval input.length)
    (he : Batch.cost (List.ofFn es) ≤ (stageEnvelopePolynomial V).eval input.length)
    (ht : (tokenBits (forestTokens (fun i => (f.wires i).val) (List.ofFn es))).length ≤
      (stageEnvelopePolynomial V).eval input.length)
    (hr : oldRoots.length ≤ (stageEnvelopePolynomial V).eval input.length) :
    forestSteps f es oldRoots ≤ (loweringPolynomial V).eval input.length := by
  have h := ForestStage.forest_steps_le (fun i => (f.wires i).val)
    (List.ofFn es) (next f) oldRoots (fun i => (f.wires i).isLt)
  change ForestStage.steps _ _ _ _ _ ≤ _
  apply h.trans
  rw [loweringPolynomial, Polynomial.eval_comp]
  apply natPolynomial_eval_mono
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_one]
  omega

def initialForestSteps (V : NPVerifier) (input : List Bool) : Nat :=
  forestSteps (Frame.initial (id : Fin (2 * V.witnessBound.eval input.length + 1) →
    Fin (2 * V.witnessBound.eval input.length + 1))) (initialExpressions V input) []

theorem initialForestSteps_le (V : NPVerifier) (input : List Bool) :
    initialForestSteps V input ≤ (loweringPolynomial V).eval input.length := by
  have hg := circuitOfVerifier_gates_le_polynomial V input
  rw [circuitOfVerifier_gate_count] at hg
  have hb := budgetPolynomial_eval V input
  have hE := stageEnvelopePolynomial_eval V input
  have ht := initial_tokens_length_le V input
  apply forestSteps_le
  · change _ + 0 ≤ _
    omega
  · omega
  · exact ht.trans (by omega)
  · simp

def transitionForestSteps (V : NPVerifier) (input : List Bool) (t : Nat) : Nat :=
  forestSteps (timeFrame V input t) (VerifierCircuit.stepExpressions V input)
    (snapshot (timeFrame V input t)).rootBits

theorem transitionForestSteps_le (V : NPVerifier) (input : List Bool) (t : Nat)
    (ht : t < V.horizon input.length) :
    transitionForestSteps V input t ≤ (loweringPolynomial V).eval input.length := by
  obtain ⟨_, hc, he, hr, htok⟩ := timeFrame_stageEnvelope V input t ht
  exact forestSteps_le V input _ _ _ hc he htok hr

def acceptanceForestSteps (V : NPVerifier) (input : List Bool) : Nat :=
  forestSteps (timeFrame V input (V.horizon input.length))
    (fun _ : Fin 1 => acceptanceExpr V input)
    (snapshot (timeFrame V input (V.horizon input.length))).rootBits

theorem acceptanceForestSteps_le (V : NPVerifier) (input : List Bool) :
    acceptanceForestSteps V input ≤ (loweringPolynomial V).eval input.length := by
  have hg := circuitOfVerifier_gates_le_polynomial V input
  rw [circuitOfVerifier_gate_count] at hg
  have hb := budgetPolynomial_eval V input
  have hE := stageEnvelopePolynomial_eval V input
  have hc := timeFrame_current_le V input (V.horizon input.length) le_rfl
  have hr := (timeFrame_lengths_le V input (V.horizon input.length) le_rfl).2.1
  have htok := acceptance_tokens_length_le V input
  apply forestSteps_le
  · omega
  · simp only [List.ofFn_succ, List.ofFn_zero, Batch.cost_cons, Batch.cost_nil, Nat.add_zero]
    omega
  · exact htok.trans (by omega)
  · exact hr.trans (by omega)

def frameInput (V : NPVerifier) (input : List Bool) (t : Nat) : TermMachine.Input :=
  AcceptanceMachine.verifierInput V input (fun i => ((timeFrame V input t).wires i).val)

theorem frameInput_dataSize_le (V : NPVerifier) (input : List Bool) (t : Nat)
    (ht : t ≤ V.horizon input.length) :
    TransitionMachine.dataSize (frameInput V input t) ≤
      2 * (stageEnvelopePolynomial V).eval input.length := by
  have hE := stageEnvelopePolynomial_eval V input
  have hr := (timeFrame_lengths_le V input t ht).2.1
  change capacity V input.length + (snapshot (timeFrame V input t)).rootBits.length ≤ _
  omega

def transitionEmissionSteps (V : NPVerifier) (input : List Bool) (t : Nat) : Nat :=
  TransitionMachine.steps (indexing V) (TransitionMachine.transitionPlan (indexing V)
    V.computation.tm.m) (frameInput V input t)

theorem transitionEmissionSteps_le (V : NPVerifier) (input : List Bool) (t : Nat)
    (ht : t ≤ V.horizon input.length) :
    transitionEmissionSteps V input t ≤ (transitionEmissionPolynomial V).eval input.length := by
  have hv : TransitionMachine.Valid (indexing V)
      (TransitionMachine.transitionPlan (indexing V) V.computation.tm.m)
      (frameInput V input t) := by
    simp [TransitionMachine.Valid, TransitionMachine.transitionPlan, frameInput,
      AcceptanceMachine.verifierInput, width]
  have h := TransitionMachine.steps_le (indexing V)
    (TransitionMachine.transitionPlan (indexing V) V.computation.tm.m) (frameInput V input t) hv
  change TransitionMachine.steps _ _ _ ≤ _
  have he : TransitionMachine.timeConstant (indexing V)
      (TransitionMachine.transitionPlan (indexing V) V.computation.tm.m) *
      (TransitionMachine.dataSize (frameInput V input t) + 1)^2 =
      (TransitionMachine.timePolynomial (indexing V)
        (TransitionMachine.transitionPlan (indexing V) V.computation.tm.m)).eval
          (TransitionMachine.dataSize (frameInput V input t)) := by
    simp [TransitionMachine.timePolynomial]
  rw [he] at h
  apply h.trans
  rw [transitionEmissionPolynomial, Polynomial.eval_comp]
  apply natPolynomial_eval_mono
  simpa using frameInput_dataSize_le V input t ht

def acceptanceEmissionSteps (V : NPVerifier) (input : List Bool) : Nat :=
  AcceptanceMachine.steps (indexing V) (AcceptancePlan.plan V)
    (frameInput V input (V.horizon input.length))

theorem acceptanceEmissionSteps_le (V : NPVerifier) (input : List Bool) :
    acceptanceEmissionSteps V input ≤ (acceptanceEmissionPolynomial V).eval input.length := by
  have hv := AcceptanceMachine.verifierInput_valid V input
    (fun i => ((timeFrame V input (V.horizon input.length)).wires i).val)
  have h := AcceptanceMachine.steps_le (indexing V) (AcceptancePlan.plan V)
    (frameInput V input (V.horizon input.length)) hv
  change AcceptanceMachine.steps _ _ _ ≤ _
  have he : AcceptanceMachine.timeConstant (indexing V) (AcceptancePlan.plan V) *
      (TransitionMachine.dataSize (frameInput V input (V.horizon input.length)) + 1)^2 =
      (AcceptanceMachine.timePolynomial (indexing V) (AcceptancePlan.plan V)).eval
        (TransitionMachine.dataSize (frameInput V input (V.horizon input.length))) := by
    simp [AcceptanceMachine.timePolynomial]
  rw [he] at h
  apply h.trans
  rw [acceptanceEmissionPolynomial, Polynomial.eval_comp]
  apply natPolynomial_eval_mono
  simpa using frameInput_dataSize_le V input (V.horizon input.length) le_rfl

def finishSteps (V : NPVerifier) (input : List Bool) : Nat :=
  let C := circuitOfVerifier V input
  CircuitFinish.totalTime C.wires C.inputs C.output.val (recordsBits C.records).length

theorem finishSteps_le (V : NPVerifier) (input : List Bool) :
    finishSteps V input ≤ (finishPolynomial V).eval input.length := by
  let C := circuitOfVerifier V input
  have hf : C.inputs ≤ C.wires := Nat.le_add_right _ _
  have h := CircuitFinish.totalTime_le C.wires C.inputs C.output.val
    (recordsBits C.records).length hf C.output.isLt
  have hg := circuitOfVerifier_gates_le_polynomial V input
  have hb := budgetPolynomial_eval V input
  have hr := (finalFrame_lengths_le V input).2.2
  have hr' : (recordsBits C.records).length ≤ (tapePolynomial V).eval input.length := by
    simpa only [snapshot, List.length_reverse, Circuit.records, finalFrame, C,
      circuitOfVerifier, Frame.toCircuit, Fragment.toCircuit] using hr
  have hc : C.wires ≤ (budgetPolynomial V).eval input.length := by
    change (2 * V.witnessBound.eval input.length + 1) +
      (circuitOfVerifier V input).gates.length ≤ _
    omega
  unfold finishSteps
  apply h.trans
  simp only [finishPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_ofNat]
  omega

theorem iterationPolynomial_eval (V : NPVerifier) (input : List Bool) :
    (iterationPolynomial V).eval input.length = V.horizon input.length *
      (1 + (transitionEmissionPolynomial V).eval input.length +
        (loweringPolynomial V).eval input.length) + 1 := by
  simp [iterationPolynomial, NPVerifier.horizon]

def iterationSteps (V : NPVerifier) (input : List Bool) : Nat :=
  (∑ t ∈ Finset.range (V.horizon input.length),
    (1 + transitionEmissionSteps V input t + transitionForestSteps V input t)) + 1

theorem iterationSteps_le (V : NPVerifier) (input : List Bool) :
    iterationSteps V input ≤ (iterationPolynomial V).eval input.length := by
  rw [iterationPolynomial_eval]
  unfold iterationSteps
  apply Nat.add_le_add_right
  calc
    _ ≤ ∑ _t ∈ Finset.range (V.horizon input.length),
        (1 + (transitionEmissionPolynomial V).eval input.length +
          (loweringPolynomial V).eval input.length) := by
      apply Finset.sum_le_sum
      intro t ht
      have hlt := Finset.mem_range.mp ht
      exact Nat.add_le_add
        (Nat.add_le_add_left (transitionEmissionSteps_le V input t (Nat.le_of_lt hlt)) 1)
        (transitionForestSteps_le V input t hlt)
    _ = _ := by simp

def knownPhaseSteps (V : NPVerifier) (input : List Bool) : Nat :=
  (VerifierFront.prepareInTime V input ()).steps +
    (2 * (2 * V.witnessBound.eval input.length + 1) + 5) + 1 +
    ValidityMachine.Full.steps (V.witnessBound.eval input.length) + initialForestSteps V input +
    iterationSteps V input + acceptanceEmissionSteps V input + acceptanceForestSteps V input +
    finishSteps V input

theorem knownPhaseSteps_le (V : NPVerifier) (input : List Bool) :
    knownPhaseSteps V input ≤ (knownPhasePolynomial V).eval input.length := by
  have hf := front_steps_le V input
  have hb := bootstrapPolynomial_eval V input.length
  have hv := validity_steps_le V input.length
  have hi := initialForestSteps_le V input
  have ht := iterationSteps_le V input
  have ha := acceptanceEmissionSteps_le V input
  have hl := acceptanceForestSteps_le V input
  have he := finishSteps_le V input
  simp only [knownPhasePolynomial, Polynomial.eval_add, Polynomial.eval_one]
  unfold knownPhaseSteps
  omega

theorem producerPolynomial_eval (V : NPVerifier) (cellTime : Polynomial Nat) (n : Nat) :
    (producerPolynomial V cellTime).eval n =
      (knownPhasePolynomial V).eval n + cellTime.eval n := by
  simp only [producerPolynomial, Polynomial.eval_add]

end BinPackingGames.Foundations.Complexity.CookLevin.ProducerTime

namespace BinPackingGames.Foundations.Complexity.CookLevin.TransitionIteration

open Turing MachineComposition StatementCircuit CircuitBatch TransitionArena
open scoped BigOperators

section Generic
variable {K Λ σ : Type} {Γ : K → Type}
variable [DecidableEq K] [Fintype σ] [DecidableEq σ]
variable [∀ k, DecidableEq (Γ k)] [∀ k, Fintype (Γ k)] [DecidableEq Λ] [Fintype Λ]
variable {inputs : Nat}

theorem steps_eq_sum (indexing : ConfigIndex.Indexing Γ Λ σ)
    (machineProgram : Λ → TM2.Stmt Γ Λ σ) (S : Nat)
    (frame : Frame inputs (indexing.width S + 1)) (remaining : Nat) :
    steps indexing machineProgram S frame remaining =
      (∑ t ∈ Finset.range remaining,
        (1 + stageSteps indexing machineProgram S
          (frame.repeat (ProducerInvariant.stepExpressions indexing machineProgram S) t))) + 1 := by
  induction remaining generalizing frame with
  | zero => simp [steps]
  | succ remaining ih =>
    rw [steps, ih, Finset.sum_range_succ']
    simp only [ProducerInvariant.step_repeat, Frame.repeat]
    omega

theorem tokens_frame_eq_forest (indexing : ConfigIndex.Indexing Γ Λ σ)
    (machineProgram : Λ → TM2.Stmt Γ Λ σ) (S : Nat)
    (frame : Frame inputs (indexing.width S + 1)) :
    tokens indexing machineProgram S (ProducerInvariant.snapshot frame) =
      PostfixAlignment.forestTokens (fun i => (frame.wires i).val)
        (List.ofFn (ProducerInvariant.stepExpressions indexing machineProgram S)) := by
  rw [tokens, ProducerInvariant.transitionTokens_eq]
  have hw : (fun i : Fin (indexing.width S + 1) =>
      (ProducerInvariant.snapshot frame).roots[i.val]?.getD 0) =
      (fun i => (frame.wires i).val) := by
    funext i
    change (List.ofFn (fun i => (frame.wires i).val))[i.val]?.getD 0 = _
    rw [List.getElem?_eq_getElem (by simpa only [List.length_ofFn] using i.isLt), List.getElem_ofFn]
    rfl
  rw [hw]

theorem lowerSteps_eq_forestSteps (indexing : ConfigIndex.Indexing Γ Λ σ)
    (machineProgram : Λ → TM2.Stmt Γ Λ σ) (S : Nat)
    (frame : Frame inputs (indexing.width S + 1)) :
    lowerSteps indexing machineProgram S frame =
      ProducerTime.forestSteps frame (ProducerInvariant.stepExpressions indexing machineProgram S)
        (encodeWords (ProducerInvariant.rootValues frame)) := by
  unfold lowerSteps ProducerTime.forestSteps
  rw [tokens_frame_eq_forest]
  have roots := ProducerInvariant.step_roots frame (ProducerInvariant.stepExpressions indexing machineProgram S)
  change ProducerInvariant.rootValues (frame.step (ProducerInvariant.stepExpressions indexing machineProgram S)) = _ at roots
  rw [roots]
  rfl

end Generic

local instance iterationTimeVerifierLabelFintype (V : NPVerifier) : Fintype V.computation.tm.Λ := V.computation.tm.ΛFin
local instance iterationTimeVerifierStateFintype (V : NPVerifier) : Fintype V.computation.tm.σ := V.computation.tm.σFin
local instance iterationTimeVerifierAlphabetFintype (V : NPVerifier) : ∀ k, Fintype (V.computation.tm.Γ k) := V.finiteAlphabet
local instance iterationTimeVerifierLabelDecidableEq (V : NPVerifier) : DecidableEq V.computation.tm.Λ := Classical.decEq _
local instance iterationTimeVerifierStateDecidableEq (V : NPVerifier) : DecidableEq V.computation.tm.σ := Classical.decEq _
local instance iterationTimeVerifierAlphabetDecidableEq (V : NPVerifier) : ∀ k, DecidableEq (V.computation.tm.Γ k) :=
  fun _ => Classical.decEq _

theorem stageSteps_verifier (V : NPVerifier) (input : List Bool) (t : Nat) :
    stageSteps (VerifierCircuit.indexing V) V.computation.tm.m
      (VerifierCircuit.capacity V input.length) (VerifierCircuit.timeFrame V input t) =
      ProducerTime.transitionEmissionSteps V input t + ProducerTime.transitionForestSteps V input t := by
  rw [stageSteps, lowerSteps_eq_forestSteps, ProducerInvariant.stepExpressions_verifier]
  rfl

theorem verifier_steps_eq (V : NPVerifier) (input : List Bool) :
    steps (VerifierCircuit.indexing V) V.computation.tm.m
      (VerifierCircuit.capacity V input.length) (VerifierCircuit.initialFrame V input)
      (V.horizon input.length) = ProducerTime.iterationSteps V input := by
  rw [steps_eq_sum, ProducerInvariant.stepExpressions_verifier]
  unfold ProducerTime.iterationSteps
  congr 1
  apply Finset.sum_congr rfl
  intro t _
  change 1 + stageSteps (VerifierCircuit.indexing V) V.computation.tm.m
    (VerifierCircuit.capacity V input.length) (VerifierCircuit.timeFrame V input t) = _
  rw [stageSteps_verifier]
  omega

theorem verifier_steps_le (V : NPVerifier) (input : List Bool) :
    steps (VerifierCircuit.indexing V) V.computation.tm.m
      (VerifierCircuit.capacity V input.length) (VerifierCircuit.initialFrame V input)
      (V.horizon input.length) ≤ (ProducerTime.iterationPolynomial V).eval input.length := by
  rw [verifier_steps_eq]
  exact ProducerTime.iterationSteps_le V input

noncomputable def verifierInPolynomialTime (V : NPVerifier) (input : List Bool)
    (base : Tape → List Bool) :
    StateTransition.EvalsToInTime
      (machine (VerifierCircuit.indexing V) V.computation.tm.m).step
      ⟨some (entry (VerifierCircuit.indexing V) V.computation.tm.m), TermMachine.initialState,
        tapes base (VerifierCircuit.capacity V input.length) (V.horizon input.length)
          (ProducerInvariant.snapshot (VerifierCircuit.initialFrame V input))⟩
      (some ⟨none, TermMachine.initialState,
        finishTapes base (VerifierCircuit.capacity V input.length)
          (ProducerInvariant.snapshot (VerifierCircuit.timeFrame V input (V.horizon input.length)))⟩)
      ((ProducerTime.iterationPolynomial V).eval input.length) where
  steps := steps (VerifierCircuit.indexing V) V.computation.tm.m
    (VerifierCircuit.capacity V input.length) (VerifierCircuit.initialFrame V input) (V.horizon input.length)
  evals_in_steps := repeatTrace (VerifierCircuit.indexing V) V.computation.tm.m base
    (VerifierCircuit.capacity V input.length) (VerifierCircuit.initialFrame V input) (V.horizon input.length)
  steps_le_m := verifier_steps_le V input

noncomputable def verifierPlacedInPolynomialTime {CallerTape CallerLabel : Type}
    [DecidableEq CallerTape] (V : NPVerifier) (input : List Bool)
    (ports : Tape ↪ CallerTape)
    (labels : Label (VerifierCircuit.indexing V) V.computation.tm.m → CallerLabel)
    (exit : Option CallerLabel)
    (target : CallerLabel → TM2.Stmt (fun _ : CallerTape => Bool) CallerLabel State)
    (code : ∀ label, target (labels label) = ForestPlacement.statement ports labels exit
      (program (VerifierCircuit.indexing V) V.computation.tm.m label))
    (ambient : CallerTape → List Bool) (base : Tape → List Bool) :
    StateTransition.EvalsToInTime (TM2.step target)
      ⟨some (labels (entry (VerifierCircuit.indexing V) V.computation.tm.m)), TermMachine.initialState,
        ForestPlacement.fill ports ambient
          (tapes base (VerifierCircuit.capacity V input.length) (V.horizon input.length)
            (ProducerInvariant.snapshot (VerifierCircuit.initialFrame V input)))⟩
      (some ⟨exit, TermMachine.initialState,
        ForestPlacement.fill ports ambient (finishTapes base (VerifierCircuit.capacity V input.length)
          (ProducerInvariant.snapshot (VerifierCircuit.timeFrame V input (V.horizon input.length))))⟩)
      ((ProducerTime.iterationPolynomial V).eval input.length) := by
  simpa only [ForestPlacement.configuration, ForestPlacement.placedLabel] using
    ForestPlacement.execution ports labels exit ambient
      (program (VerifierCircuit.indexing V) V.computation.tm.m) target code
      (verifierInPolynomialTime V input base)

end BinPackingGames.Foundations.Complexity.CookLevin.TransitionIteration

end

end OAI
