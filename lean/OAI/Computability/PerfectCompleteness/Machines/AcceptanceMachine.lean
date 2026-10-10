import OAI.Computability.PerfectCompleteness.Machines.InitializationTemplateLemmas
import OAI.Computability.PerfectCompleteness.Machines.OrClosure
import OAI.Computability.PerfectCompleteness.Machines.TransitionMachine

namespace OAI


namespace UniqueGamesTheorem.Foundations.Complexity.CookLevin.AcceptanceMachine


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

omit [DecidableEq K] [Fintype σ] [DecidableEq σ] [∀ k, DecidableEq (Γ k)]
    [∀ k, Fintype (Γ k)] [DecidableEq Λ] [Fintype Λ] in
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

omit [DecidableEq K] [Fintype σ] [DecidableEq σ] [∀ k, DecidableEq (Γ k)]
    [∀ k, Fintype (Γ k)] [DecidableEq Λ] [Fintype Λ] in
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

noncomputable section Verifier

open VerifierCircuit AcceptanceTemplate

local instance (V : NPVerifier) : Fintype V.computation.tm.Λ := V.computation.tm.ΛFin
local instance (V : NPVerifier) : Fintype V.computation.tm.σ := V.computation.tm.σFin
local instance (V : NPVerifier) : ∀ k, Fintype (V.computation.tm.Γ k) := V.finiteAlphabet
local instance (V : NPVerifier) : DecidableEq V.computation.tm.Λ := Classical.decEq _
local instance (V : NPVerifier) : DecidableEq V.computation.tm.σ := Classical.decEq _
local instance (V : NPVerifier) : ∀ k, DecidableEq (V.computation.tm.Γ k) :=
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

end Verifier

end UniqueGamesTheorem.Foundations.Complexity.CookLevin.AcceptanceMachine

end OAI
