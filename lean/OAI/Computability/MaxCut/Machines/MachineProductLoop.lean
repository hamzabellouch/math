import Mathlib
import OAI.Computability.MaxCut.Machines.RuntimeSpace
import OAI.Computability.MaxCut.Machines.MachineProductProgram

namespace OAI

/-! Whole tuple traversal of the concrete product program. The odometer theorem
is instantiated by the proved actual row trace, not by an assumed row machine. -/

namespace MaxCutGames.Explicit.MachineProductLoop

open Turing
open MaxCutGames.Foundations
open Complexity Hastad
open MachineComposition
open MachineProductProgram

variable {q t : Nat}

noncomputable section

structure BaseReady (H : Target.Instance q) (base : Tape t → List Bool) : Prop where
  work : ∀ b, MachineProductField.Ready (MachineProductRow.fieldSlots (rowSlots t) b) base
  table : base .formula = encodeWords (ProductMachineSemantics.inputTable H)
  vertices : base (auxiliary t 0) = encodeWord H.vertices
  alphabet : base (auxiliary t 7) = encodeWord q

def tupleTapes (H : Target.Instance q) (base : Tape t → List Bool)
    (edges : Fin t → Fin H.constraints.length) (out : List Bool) : Tape t → List Bool :=
  SourceOdometerSchedule.setDigits H.constraints.length (fun i => (edges i).val)
    (SourceOdometerSchedule.setAcc (Sum.inl (6 : Fin 10)) base out)

theorem tupleTapes_frame (H : Target.Instance q) (base : Tape t → List Bool)
    (edges : Fin t → Fin H.constraints.length) (out : List Bool) (k : Tape t)
    (hc : ∀ i, k ≠ .current i) (hr : ∀ i, k ≠ .remaining i)
    (ha : k ≠ accumulator t) : tupleTapes H base edges out k = base k := by
  cases k with
  | current i => exact (hc i rfl).elim
  | remaining i => exact (hr i rfl).elim
  | extra x =>
    simp only [tupleTapes, SourceOdometerSchedule.setDigits, SourceOdometerSchedule.setAcc]
    exact Function.update_of_ne ha _ _
  | _ => simp [tupleTapes, SourceOdometerSchedule.setDigits, SourceOdometerSchedule.setAcc]

@[simp] theorem tupleTapes_current (H : Target.Instance q) (base : Tape t → List Bool)
    (edges : Fin t → Fin H.constraints.length) (out : List Bool) (i : Fin t) :
    tupleTapes H base edges out (.current i) = encodeWord (edges i).val := by
  simp [tupleTapes, SourceOdometerSchedule.setDigits, i.isLt]

@[simp] theorem tupleTapes_accumulator (H : Target.Instance q) (base : Tape t → List Bool)
    (edges : Fin t → Fin H.constraints.length) (out : List Bool) :
    tupleTapes H base edges out (accumulator t) = out := by
  simp [tupleTapes, accumulator, auxiliary, SourceOdometerSchedule.setDigits, SourceOdometerSchedule.setAcc]

theorem tupleTapes_ready (H : Target.Instance q) (base : Tape t → List Bool)
    (ready : BaseReady H base) (edges : Fin t → Fin H.constraints.length) (out : List Bool) :
    MachineProductRow.Ready (rowSlots t) (ProductMachineSemantics.inputTable H)
      (fun i => (edges i).val) (fun b => if b then q else H.vertices) (tupleTapes H base edges out) := by
  have other (k : Tape t) (hc : ∀ i, k ≠ .current i) (hr : ∀ i, k ≠ .remaining i)
      (ha : k ≠ accumulator t) := tupleTapes_frame H base edges out k hc hr ha
  constructor
  · intro b
    have work := ready.work b
    constructor
    · change tupleTapes H base edges out .index = []
      rw [other .index (by simp) (by simp) (by simp [accumulator, auxiliary])]
      exact work.query
    · change tupleTapes H base edges out .work = []
      rw [other .work (by simp) (by simp) (by simp [accumulator, auxiliary])]
      exact work.scan
    · change tupleTapes H base edges out .scratch = []
      rw [other .scratch (by simp) (by simp) (by simp [accumulator, auxiliary])]
      exact work.gatherScratch
    · intro i
      change tupleTapes H base edges out (.field i 0) = []
      rw [other (.field i 0) (by simp) (by simp) (by simp [accumulator, auxiliary])]
      exact work.fields i
    · change tupleTapes H base edges out (auxiliary t 1) = []
      rw [other _ (by simp [auxiliary]) (by simp [auxiliary]) (by simp [accumulator, auxiliary])]
      exact work.accA
    · change tupleTapes H base edges out (auxiliary t 2) = []
      rw [other _ (by simp [auxiliary]) (by simp [auxiliary]) (by simp [accumulator, auxiliary])]
      exact work.accB
    · change tupleTapes H base edges out (auxiliary t 3) = []
      rw [other _ (by simp [auxiliary]) (by simp [auxiliary]) (by simp [accumulator, auxiliary])]
      exact work.counter
    · change tupleTapes H base edges out (auxiliary t 4) = []
      rw [other _ (by simp [auxiliary]) (by simp [auxiliary]) (by simp [accumulator, auxiliary])]
      exact work.hornerScratch
    · change tupleTapes H base edges out (auxiliary t 5) = []
      rw [other _ (by simp [auxiliary]) (by simp [auxiliary]) (by simp [accumulator, auxiliary])]
      exact work.output
  · change tupleTapes H base edges out .formula = _
    rw [other .formula (by simp) (by simp) (by simp [accumulator, auxiliary])]
    exact ready.table
  · intro i; exact tupleTapes_current H base edges out i
  · intro b
    cases b
    · change tupleTapes H base edges out (auxiliary t 0) = _
      rw [other _ (by simp [auxiliary]) (by simp [auxiliary]) (by simp [accumulator, auxiliary])]
      exact ready.vertices
    · change tupleTapes H base edges out (auxiliary t 7) = _
      rw [other _ (by simp [auxiliary]) (by simp [auxiliary]) (by simp [accumulator, auxiliary])]
      exact ready.alphabet

def rowBits (H : Target.Instance q) (edges : Fin t → Fin H.constraints.length) : List Bool :=
  MachineProductRow.rowBits (ProductMachineSemantics.fieldValue H edges)
    (ProductMachineSemantics.commands q t)

theorem input_length (H : Target.Instance q) :
    (gameBits H).length = H.vertices + q + H.constraints.length + 3 +
      (encodeWords (ProductMachineSemantics.inputTable H)).length := by
  simp [gameBits, gameWords, ProductMachineSemantics.inputTable,
    encodeWords, encodeWord_length, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] ; omega

def bodyBound (H : Target.Instance q) (t : Nat) : Nat :=
  (q ^ t + 2) * (MachineProductBounds.fieldPolynomial t).eval (gameBits H).length

/-- The actual row execution supplies the local obligation of the generic
odometer schedule. Its cost is uniformly polynomial in the original bits. -/
theorem bodyTrace (H : Target.Instance q) (base : Tape t → List Bool) (ready : BaseReady H base) :
    SourceOdometerSchedule.BodyTrace (program q t) (rowMain q t) (nextCheck q t 0)
      ((), ()) (Sum.inl (6 : Fin 10)) base (rowBits (t := t) H) (bodyBound H t) := by
  intro edges out
  let indices := fun i => (edges i).val
  let radices := fun b : Bool => if b then q else H.vertices
  let fields := ProductMachineSemantics.fields H edges
  let digits := fun c => ProductMachineSemantics.reverseDigits (fields c)
  let frame := tupleTapes H base edges out
  have hready := tupleTapes_ready H base ready edges out
  have selected := ProductMachineSemantics.selected H edges
  have reversed : ∀ c ∈ ProductMachineSemantics.commands q t, ∀ i : Fin t,
      digits c i.val = fields c i.rev := by
    intro c hc i
    exact ProductMachineSemantics.reverseDigits_at _ _
  have run := MachineProductRow.rowTrace (rowSlots t) (ProductMachineSemantics.inputTable H)
    (q + 2) indices radices (ProductMachineSemantics.commands q t) fields digits selected reversed
    Label.row (some (nextCheck q t 0)) (program q t) (fun _ => rfl) frame hready ()
  have len := input_length H
  have tableBound : (encodeWords (ProductMachineSemantics.inputTable H)).length ≤ (gameBits H).length := by omega
  have indexBound (i : Fin t) : indices i ≤ (gameBits H).length := by
    have h := (edges i).isLt; dsimp [indices]; omega
  have radixBound (b : Bool) : radices b ≤ (gameBits H).length := by
    cases b <;> dsimp [radices] <;> omega
  have digitBound (c : MachineProductRow.Command t) (hc : c ∈ ProductMachineSemantics.commands q t)
      (i : Nat) (hi : i < t) : digits c i ≤ (gameBits H).length := by
    rw [show digits c i = fields c (Fin.rev ⟨i, hi⟩) from
      ProductMachineSemantics.reverseDigits_at _ ⟨i, hi⟩]
    have h := ProductMachineSemantics.fields_lt H edges c hc (Fin.rev ⟨i, hi⟩)
    have hr := radixBound c.1
    dsimp [radices, fields] at hr ⊢
    omega
  have bound := MachineProductBounds.row_steps_le (rowSlots t) (ProductMachineSemantics.inputTable H)
    (q + 2) indices radices (ProductMachineSemantics.commands q t) fields digits selected
    frame hready (gameBits H).length tableBound indexBound radixBound digitBound
  rw [ProductMachineSemantics.commands_length] at bound
  refine ⟨_, bound, ?_⟩
  have hframe : Function.update frame (MachineProductRow.outputTape (rowSlots t))
      ((rowBits H edges).reverse ++ frame (MachineProductRow.outputTape (rowSlots t))) =
      tupleTapes H base edges ((rowBits H edges).reverse ++ out) := by
    change Function.update frame (accumulator t)
      ((rowBits H edges).reverse ++ frame (accumulator t)) = _
    rw [show frame (accumulator t) = out from tupleTapes_accumulator H base edges out]
    simp only [frame, tupleTapes, SourceOdometerSchedule.setDigits_setAcc]
    simp [SourceOdometerSchedule.setAcc, accumulator, auxiliary]
  dsimp only at run
  change _ = some (⟨some (nextCheck q t 0), (((), ()), none),
    Function.update frame (MachineProductRow.outputTape (rowSlots t))
      ((rowBits H edges).reverse ++ frame (MachineProductRow.outputTape (rowSlots t)))⟩ : (machine q t).Cfg) at run
  erw [hframe] at run
  exact run

/-- Complete positive-radix tuple traversal with actual row bodies discharged. -/
theorem traversalInTime (H : Target.Instance q) (base : Tape t → List Bool) (ready : BaseReady H base) :
    Nonempty (StateTransition.EvalsToInTime (TM2.step (program q t))
      (SourceOdometerSchedule.initialConfiguration (m := H.constraints.length) t (rowMain q t) ((), ()) base)
      (some (SourceOdometerSchedule.finalConfiguration (nextCheck q t t) ((), ())
        (Sum.inl (6 : Fin 10)) base (rowBits (t := t) H)))
      ((bodyBound H t + 2 * t) * H.constraints.length ^ t)) := by
  apply SourceOdometerSchedule.traversalInTime (program q t) (rowMain q t)
    (nextCheck q t) (resetAt q t) ((), ()) (Sum.inl (6 : Fin 10))
    (List.length_pos_iff.mpr H.nonempty) (bodyBound H t) base (rowBits (t := t) H)
  · intro i hi
    simp [nextCheck, resetAt, hi, program, SourceOdometerSchedule.currentAt,
      SourceOdometerSchedule.remainingAt]
  · intro i hi
    simp [nextCheck, resetAt, hi, program, SourceOdometerSchedule.currentAt,
      SourceOdometerSchedule.remainingAt]
  · exact bodyTrace H base ready

end

end MaxCutGames.Explicit.MachineProductLoop

/-! Exact final cleanup and binary-output identification for the product
controller. The final runtime bound is derived from actual stack lengths. -/

namespace MaxCutGames.Explicit.MachineProductFinish

open Turing
open MaxCutGames.Foundations
open Complexity Hastad
open MachineComposition
open MachineProductProgram

variable {q t : Nat}

noncomputable section

theorem base_ready (H : Target.Instance q) (t : Nat) :
    MachineProductLoop.BaseReady H (MachineProductHeaders.baseTapes H t) := by
  constructor
  · intro b
    constructor <;> simp [MachineProductHeaders.baseTapes, MachineProductHeaders.frame,
      MachineProductRow.fieldSlots, MachineProductRow.fieldRole, rowSlots] <;> (intros; rfl)
  · rfl
  · simp [MachineProductHeaders.baseTapes, MachineProductHeaders.frame, auxiliary]
  · simp [MachineProductHeaders.baseTapes, MachineProductHeaders.frame, auxiliary]

def afterRows (H : Target.Instance q) (t : Nat) : (machine q t).Cfg :=
  SourceOdometerSchedule.finalConfiguration (nextCheck q t t) ((), ())
    (Sum.inl (6 : Fin 10)) (MachineProductHeaders.baseTapes H t) (MachineProductLoop.rowBits (t := t) H)

theorem afterRows_output (H : Target.Instance q) (t : Nat) :
    (afterRows H t).stk (output t) = [] := by
  simp [afterRows, SourceOdometerSchedule.finalConfiguration, SourceOdometerSchedule.configuration,
    SourceOdometerSchedule.setDigits, SourceOdometerSchedule.setAcc, output, auxiliary,
    MachineProductHeaders.baseTapes, MachineProductHeaders.frame]
  rfl

theorem allRows_eq (H : Target.Instance q) (t : Nat) :
    (MachineTupleOdometer.tupleOrder H.constraints.length t).flatMap (MachineProductLoop.rowBits (t := t) H) =
      ProductMachineSemantics.allRowsBits H t := by
  simp only [MachineTupleOdometer.tupleOrder, ProductMachineSemantics.allRowsBits,
    List.ofFn_eq_map, List.flatMap_map, MachineProductLoop.rowBits]

theorem afterRows_accumulator (H : Target.Instance q)
    (presentation : MachineOutputContract.SimpleBipartite H) (t : Nat) (ht : 0 < t) :
    ((afterRows H t).stk (accumulator t)).reverse =
      gameBits (ProductPaddedOutput.output H presentation t ht) := by
  change ((SourceOdometerSchedule.allBits (MachineProductLoop.rowBits (t := t) H)).reverse ++
    MachineProductHeaders.baseTapes H t (accumulator t)).reverse = _
  rw [MachineProductHeaders.baseTapes, MachineProductHeaders.frame_accumulator,
    List.reverse_append, List.reverse_reverse, List.reverse_reverse]
  rw [SourceOdometerSchedule.allBits, allRows_eq]
  exact ProductMachineSemantics.gameBits_eq H presentation t ht

/-- The entry hop reaches the actual cleanup list, then all work is drained,
the accumulator is reversed, and the final finite register is reset. -/
def finishInTime (base : Tape t → List Bool) (emptyOutput : base (output t) = []) :
    StateTransition.EvalsToInTime (TM2.step (program q t))
      ⟨some .finishStart, (((), ()), none), base⟩
      (some ⟨none, (((), ()), none),
        SourceRuntimeFinish.canonicalTapes (output t) (base (accumulator t)).reverse⟩)
      (1 + SourceRuntimeFinish.finishCost (clearKeys t) (accumulator t) base) := by
  have enter : StateTransition.EvalsToInTime (TM2.step (program q t))
      ⟨some .finishStart, (((), ()), none), base⟩
      (some ⟨SourceRuntimeFinish.entry (clearKeys t) Label.finish, (((), ()), none), base⟩) 1 := by
    refine ⟨⟨1, ?_⟩, Nat.le_refl _⟩
    change some (TM2.stepAux (program q t .finishStart) _ _) = _
    simp only [program, MaxCutGames.Reduction.MachineTransfer.exitAt]
    split <;> simp_all [TM2.stepAux]
  have finish := SourceRuntimeFinish.finishInTime (clearKeys t) (accumulator t) (output t)
    (by simp [accumulator, output, auxiliary])
    (by simp) (by simp) (by intro k h1 h2; simp [h1, h2])
    ((), ()) Label.finish none (program q t) (fun _ => rfl) base emptyOutput ((), ()) none
  have joined := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ enter finish
  exact { toEvalsTo := joined.toEvalsTo
          steps_le_m := by simpa only [Nat.add_comm] using joined.steps_le_m }

/-- A uniform bound on the real cleanup work, from bounds on actual stacks. -/
theorem finishCost_le_uniform (base : Tape t → List Bool) (bound : Nat)
    (bounded : ∀ k, (base k).length ≤ bound) :
    SourceRuntimeFinish.finishCost (clearKeys t) (accumulator t) base ≤
      ((clearKeys t).length + 1) * bound + (clearKeys t).length + 2 := by
  have clear := MachineDrainMany.steps_le_uniform (clearKeys t) base bound bounded
  have acc := bounded (accumulator t)
  unfold SourceRuntimeFinish.finishCost
  rw [Nat.add_mul, Nat.one_mul]
  rw [Nat.mul_add, Nat.mul_one] at clear
  omega

theorem finish_afterRows (H : Target.Instance q)
    (presentation : MachineOutputContract.SimpleBipartite H) (t : Nat) (ht : 0 < t) :
    Nonempty (StateTransition.EvalsToInTime (machine q t).step (afterRows H t)
      (some (haltList (machine q t) (gameBits (ProductPaddedOutput.output H presentation t ht))))
      (1 + SourceRuntimeFinish.finishCost (clearKeys t) (accumulator t) (afterRows H t).stk)) := by
  have run := finishInTime (q := q) (afterRows H t).stk (afterRows_output H t)
  erw [afterRows_accumulator H presentation t ht] at run
  have hstart : (afterRows H t).l = some .finishStart := by simp [afterRows,
    SourceOdometerSchedule.finalConfiguration, SourceOdometerSchedule.configuration, nextCheck]
  have hstate : (afterRows H t).var = (((), ()), none) := rfl
  have halt : (⟨none, (((), ()), none), SourceRuntimeFinish.canonicalTapes (output t)
      (gameBits (ProductPaddedOutput.output H presentation t ht))⟩ : (machine q t).Cfg) =
      haltList (machine q t) (gameBits (ProductPaddedOutput.output H presentation t ht)) := by
    unfold haltList SourceRuntimeFinish.canonicalTapes
    congr 1
    funext k
    by_cases hk : k = output t
    · subst k
      simp only [machine]
      erw [Function.update_self]
      rfl
    · simp only [machine]
      erw [Function.update_of_ne hk, dite_eq_right hk]
  erw [halt] at run
  have hcfg : (⟨some .finishStart, (((), ()), none), (afterRows H t).stk⟩ : (machine q t).Cfg) =
      afterRows H t := by cases h : afterRows H t; simp_all
  erw [hcfg] at run
  exact ⟨run⟩

end

end MaxCutGames.Explicit.MachineProductFinish

/-! The complete explicit product computation. Every execution phase is supplied
by the actual controller; the cleanup bound follows from the space reached by
its actual prefix. The exponent and alphabet enter only the fixed program. -/

namespace MaxCutGames.Explicit.MachineProductRuntime

open Turing
open MaxCutGames.Foundations Target Complexity Hastad
open MachineProductProgram

noncomputable section

def loopPolynomial (q t : Nat) : Polynomial Nat :=
  (Polynomial.C (q ^ t + 2) * MachineProductBounds.fieldPolynomial t +
    Polynomial.C (2 * t)) * Polynomial.X ^ t

theorem loop_budget {q : Nat} (H : Instance q) (t : Nat) :
    (MachineProductLoop.bodyBound H t + 2 * t) * H.constraints.length ^ t ≤
      (loopPolynomial q t).eval (gameBits H).length := by
  have hlen := MachineProductLoop.input_length H
  have hm : H.constraints.length ≤ (gameBits H).length := by omega
  simp only [loopPolynomial, Polynomial.eval_mul, Polynomial.eval_add,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hm t)

def prefixPolynomial (q t : Nat) : Polynomial Nat :=
  MachineProductHeaders.timePolynomial t + loopPolynomial q t

/-- Actual header initialization followed by every product row and odometer step. -/
def prefixInTime {q : Nat} (H : Instance q) (t : Nat) :
    StateTransition.EvalsToInTime (machine q t).step
      (initList (machine q t) (gameBits H))
      (some (MachineProductFinish.afterRows H t))
      ((prefixPolynomial q t).eval (gameBits H).length) := by
  let first := MachineProductHeaders.inPolynomialTime H t
  let loop := Classical.choice (MachineProductLoop.traversalInTime H
    (MachineProductHeaders.baseTapes H t) (MachineProductFinish.base_ready H t))
  let second : StateTransition.EvalsToInTime (machine q t).step
      (SourceOdometerSchedule.initialConfiguration (m := H.constraints.length)
        t (rowMain q t) ((), ()) (MachineProductHeaders.baseTapes H t))
      (some (MachineProductFinish.afterRows H t))
      ((loopPolynomial q t).eval (gameBits H).length) := {
    toEvalsTo := loop.toEvalsTo
    steps_le_m := loop.steps_le_m.trans (loop_budget H t) }
  let joined := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ first second
  exact {
    toEvalsTo := joined.toEvalsTo
    steps_le_m := by
      simpa only [prefixPolynomial, Polynomial.eval_add, Nat.add_comm]
        using joined.steps_le_m }

def timePolynomial (q t : Nat) : Polynomial Nat :=
  SourceRuntimeSpace.completedTime (machine q t) (clearKeys t).length
    (prefixPolynomial q t) + 1

/-- The complete run produces the literal full-table target code, clears all
private stacks, resets its finite state, and halts. -/
def outputInTime {q : Nat} (H : Instance q)
    (presentation : MachineOutputContract.SimpleBipartite H) (t : Nat) (ht : 0 < t) :
    TM2OutputsInTime (machine q t) (gameBits H)
      (some (gameBits (ProductPaddedOutput.output H presentation t ht)))
      ((timePolynomial q t).eval (gameBits H).length) := by
  let initialRun := prefixInTime H t
  let finish := Classical.choice (MachineProductFinish.finish_afterRows H presentation t ht)
  let whole := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ initialRun finish
  have keepAccumulator : accumulator t ∉ clearKeys t := by simp
  have keepOutput : output t ∉ clearKeys t := by simp
  have covers (k : Tape t) (ha : k ≠ accumulator t) (ho : k ≠ output t) :
      k ∈ clearKeys t := (mem_clearKeys t k).mpr ⟨ha, ho⟩
  have bound : SourceRuntimeFinish.finishCost (clearKeys t) (accumulator t)
      (MachineProductFinish.afterRows H t).stk ≤ (gameBits H).length +
        (prefixPolynomial q t).eval (gameBits H).length *
          (@Fintype.card (machine q t).K (machine q t).kFin * Runtime.programPushBound (machine q t)) +
        (clearKeys t).length + 2 :=
    SourceRuntimeSpace.finishCost_le_of_prefix (machine q t) (gameBits H)
    initialRun (clearKeys t) (accumulator t) (output t)
    keepAccumulator keepOutput covers
    (MachineProductFinish.afterRows H t).stk (MachineProductFinish.afterRows_output H t)
    (fun _ => rfl)
  change StateTransition.EvalsToInTime (machine q t).step _
    (some (haltList (machine q t) _)) _
  refine { toEvalsTo := whole.toEvalsTo, steps_le_m := whole.steps_le_m.trans ?_ }
  simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_one,
    SourceRuntimeSpace.completedTime_eval]
  omega

/-- The bipartition is proof-side data. Its codec is exactly the underlying
instance code and the fixed program does not inspect it. -/
abbrev Input (q : Nat) := Σ H : Instance q, MachineOutputContract.SimpleBipartite H

def construct {q : Nat} (t : Nat) (ht : 0 < t) (H : Input q) : Instance (q ^ t) :=
  ProductPaddedOutput.output H.1 H.2 t ht

def computation (q t : Nat) (ht : 0 < t) :
    TM2ComputableInPolyTime (fun H : Input q => gameBits H.1) gameBits
      (construct t ht) where
  tm := machine q t
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := timePolynomial q t
  outputsFun H := by
    change TM2OutputsInTime (machine q t) ((gameBits H.1).map id)
      (some ((gameBits (construct t ht H)).map id)) _
    have hi := @List.map_id ((machine q t).Γ (machine q t).k₀) (gameBits H.1)
    have ho := @List.map_id ((machine q t).Γ (machine q t).k₁) (gameBits (construct t ht H))
    simp only [hi, ho]
    exact outputInTime H.1 H.2 t ht

theorem finiteAlphabet (q t : Nat) (ht : 0 < t) :
    MachineFiniteAlphabet.FiniteAlphabet (computation q t ht).tm :=
  MachineFiniteAlphabet.of_bool _ (fun _ => rfl)

variable {A : Type} {q : Nat} {encode : A → List Bool} {f : A → Instance q}

def certify (upstream : TM2ComputableInPolyTime encode gameBits f)
    (presentation : ∀ a, MachineOutputContract.SimpleBipartite (f a)) :
    TM2ComputableInPolyTime encode (fun H : Input q => gameBits H.1)
      (fun a => ⟨f a, presentation a⟩) where
  tm := upstream.tm
  inputAlphabet := upstream.inputAlphabet
  outputAlphabet := upstream.outputAlphabet
  time := upstream.time
  outputsFun := upstream.outputsFun

/-- Direct composition with an actual preceding simple-bipartite producer. -/
def compose (upstream : TM2ComputableInPolyTime encode gameBits f)
    (presentation : ∀ a, MachineOutputContract.SimpleBipartite (f a))
    (t : Nat) (ht : 0 < t) :
    TM2ComputableInPolyTime encode gameBits
      (fun a => ProductPaddedOutput.output (f a) (presentation a) t ht) :=
  MachineSequential.composeBits (certify upstream presentation) (computation q t ht)

theorem compose_finiteAlphabet (upstream : TM2ComputableInPolyTime encode gameBits f)
    (presentation : ∀ a, MachineOutputContract.SimpleBipartite (f a))
    (t : Nat) (ht : 0 < t) (finite : MachineFiniteAlphabet.FiniteAlphabet upstream.tm) :
    MachineFiniteAlphabet.FiniteAlphabet (compose upstream presentation t ht).tm :=
  MachineFiniteAlphabet.composeBits (certify upstream presentation) (computation q t ht)
    finite (finiteAlphabet q t ht)

end

end MaxCutGames.Explicit.MachineProductRuntime

end OAI
