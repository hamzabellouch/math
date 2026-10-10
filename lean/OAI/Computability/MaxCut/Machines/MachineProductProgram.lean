import Mathlib
import OAI.Computability.MaxCut.Machines.MachineProductGatherBounds
import OAI.Computability.MaxCut.Machines.MachineInitialHeaders
import OAI.Computability.MaxCut.PCP.LoopOrder

namespace OAI

namespace MaxCutGames.Explicit.MachineProductProgram

open Turing
open MaxCutGames.Foundations
open Complexity Hastad
open MaxCutGames.Reduction.MachineTransfer

abbrev Extra (t : Nat) := Fin 10 ⊕ Fin (t + 1)
abbrev Tape (t : Nat) := SourceContextLoad.Tape t (Extra t)
abbrev State := MachineHorner.State Unit

def auxiliary (t : Nat) (i : Fin 10) : Tape t := .extra (.inl i)
def constantDigit (t : Nat) (i : Fin (t + 1)) : Tape t := .extra (.inr i)
def accumulator (t : Nat) : Tape t := auxiliary t 6
def output (t : Nat) : Tape t := auxiliary t 9

def rowRole (t : Nat) : MachineProductRow.Layout t → Tape t
  | .inl (.inl (.inl 0)) => .formula
  | .inl (.inl (.inl 1)) => .index
  | .inl (.inl (.inl 2)) => .work
  | .inl (.inl (.inl 3)) => .scratch
  | .inl (.inl (.inr (.inl i))) => .current i
  | .inl (.inl (.inr (.inr i))) => .field i 0
  | .inl (.inr i) => auxiliary t (Fin.castLE (by omega) i)
  | .inr _ => auxiliary t 7

private def decodeRow_inline_MachineProductProgram (t : Nat) : Tape t → Option (MachineProductRow.Layout t)
  | .formula => some (.inl (.inl (.inl 0)))
  | .index => some (.inl (.inl (.inl 1)))
  | .work => some (.inl (.inl (.inl 2)))
  | .scratch => some (.inl (.inl (.inl 3)))
  | .current i => some (.inl (.inl (.inr (.inl i))))
  | .field i s => if s = 0 then some (.inl (.inl (.inr (.inr i)))) else none
  | .extra (.inl i) => if h : i.val < 7 then some (.inl (.inr ⟨i.val, h⟩))
      else if i = 7 then some (.inr ()) else none
  | _ => none

private theorem decodeRow_role_inline_MachineProductProgram (t : Nat) (i : MachineProductRow.Layout t) :
    decodeRow_inline_MachineProductProgram t (rowRole t i) = some i := by
  rcases i with (((i | (i | i)) | i) | i)
  · fin_cases i <;> rfl
  · rfl
  · simp [decodeRow_inline_MachineProductProgram, rowRole]
  · simp [rowRole, auxiliary, decodeRow_inline_MachineProductProgram, i.isLt]
  · cases i; rfl

def rowSlots (t : Nat) : MachineProductRow.Layout t ↪ Tape t where
  toFun := rowRole t
  inj' := by
    intro a b h
    have d := congrArg (decodeRow_inline_MachineProductProgram t) h
    exact Option.some.inj (by simpa only [decodeRow_role_inline_MachineProductProgram] using d)

def powerRole (t : Nat) (edgeCount : Bool) : MachineHorner.Layout (t + 1) → Tape t
  | .inl 0 => auxiliary t (if edgeCount then 8 else 0)
  | .inl 1 => auxiliary t 1
  | .inl 2 => auxiliary t 2
  | .inl 3 => auxiliary t 5
  | .inl 4 => auxiliary t 3
  | .inl 5 => auxiliary t 4
  | .inr i => constantDigit t i

theorem powerRole_injective (t : Nat) (edgeCount : Bool) : Function.Injective (powerRole t edgeCount) := by
  intro a b h
  cases a with
  | inl a =>
    cases b with
    | inl b => fin_cases a <;> fin_cases b <;> cases edgeCount <;> simp_all [powerRole, auxiliary]
    | inr b => fin_cases a <;> cases edgeCount <;> simp [powerRole, auxiliary, constantDigit] at h
  | inr a =>
    cases b with
    | inl b => fin_cases b <;> cases edgeCount <;> simp [powerRole, auxiliary, constantDigit] at h
    | inr b => simpa [powerRole, constantDigit] using h

def powerSlots (t : Nat) (edgeCount : Bool) : MachineHorner.Layout (t + 1) ↪ Tape t :=
  ⟨powerRole t edgeCount, powerRole_injective t edgeCount⟩

def initRole (t : Nat) : MachineOdometerInit.Tape t → Tape t
  | .radix => auxiliary t 8
  | .scratch => .copyScratch
  | .current i => .current i
  | .remaining i => .remaining i

theorem initRole_injective (t : Nat) : Function.Injective (initRole t) := by
  intro a b h
  cases a <;> cases b <;> simp_all [initRole, auxiliary]

def seedCommands (t : Nat) : List (MachineProductSeed.Command (Tape t)) :=
  List.ofFn (fun i : Fin (t + 1) => (constantDigit t i, encodeWord (MachineProductPower.digits i.val)))

noncomputable def clearKeys (t : Nat) : List (Tape t) :=
  Finset.univ.toList.filter (fun k => decide (k ≠ accumulator t ∧ k ≠ output t))

@[simp] theorem mem_clearKeys (t : Nat) (k : Tape t) :
    k ∈ clearKeys t ↔ k ≠ accumulator t ∧ k ≠ output t := by
  simp [clearKeys]

noncomputable section

inductive Label (q t : Nat)
  | headerStart (i : Fin 3)
  | headerRead (i : Fin 3)
  | seedStart
  | seed (inner : MachineProductSeed.Label (seedCommands t))
  | power (edgeCount : Bool) (inner : MachineProductPower.Label t)
  | alphabetHeader
  | initialize (inner : MachineOdometerInit.Label t)
  | row (inner : MachineProductRow.Label (rowSlots t) (ProductMachineSemantics.commands q t))
  | check (i : Fin t)
  | reset (i : Fin t)
  | finishStart
  | finish (inner : SourceRuntimeFinish.Label (clearKeys t))
  deriving DecidableEq, Fintype

def headerDestination (t : Nat) : Fin 3 → Tape t
  | 0 => auxiliary t 0
  | 1 => auxiliary t 7
  | 2 => auxiliary t 8

def rowMain (q t : Nat) : Label q t :=
  .row (.inl (MachineProductRow.localMain (rowSlots t) (ProductMachineSemantics.sourceCommand t)))

def nextCheck (q t i : Nat) : Label q t := if h : i < t then .check ⟨i, h⟩ else .finishStart

def resetAt (q t i : Nat) : Label q t := if h : i < t then .reset ⟨i, h⟩ else .finishStart

def headerNext (q t : Nat) (i : Fin 3) : Label q t :=
  if h : i.val + 1 < 3 then .headerStart ⟨i.val + 1, h⟩ else .seedStart

def program (q t : Nat) : Label q t → TM2.Stmt (fun _ : Tape t => Bool) (Label q t) State
  | .headerStart i => SourceMachine.fieldStart (headerDestination t i) (.headerRead i)
  | .headerRead i => SourceMachine.fieldLoop .formula (headerDestination t i)
      (.headerRead i) (some (headerNext q t i))
  | .seedStart => exitAt .formula (MachineProductSeed.entry (seedCommands t) Label.seed
      (some (.power false (.inl .start))))
  | .seed inner => MachineProductSeed.instruction (seedCommands t) Label.seed
      (some (.power false (.inl .start))) inner
  | .power false inner => MachineProductPower.instruction (powerSlots t false) (accumulator t)
      (Label.power false) (some .alphabetHeader) inner
  | .power true inner => MachineProductPower.instruction (powerSlots t true) (accumulator t)
      (Label.power true) (some (MachineOdometerInit.labelAt Label.initialize 0)) inner
  | .alphabetHeader => MaxCutGames.Reduction.MachineSubstitution.pushWord (accumulator t)
      (encodeWord (q ^ t)) (.goto fun _ => .power true (.inl .start))
  | .initialize inner => MachineOdometerInit.statement (initRole t) Label.initialize
      (some (rowMain q t)) inner
  | .row inner => MachineProductRow.instruction (rowSlots t) (q + 2)
      (ProductMachineSemantics.commands q t) Label.row (some (nextCheck q t 0)) inner
  | .check i => MachineTupleOdometer.increment (.current i) (.remaining i)
      (rowMain q t) (.reset i)
  | .reset i => MachineTupleOdometer.reset (.current i) (.remaining i)
      (.reset i) (nextCheck q t (i.val + 1))
  | .finishStart => exitAt .formula (SourceRuntimeFinish.entry (clearKeys t) Label.finish)
  | .finish inner => SourceRuntimeFinish.statement (clearKeys t) (accumulator t) (output t)
      ((), ()) Label.finish none inner

def machine (q t : Nat) : FinTM2 where
  K := Tape t
  k₀ := .formula
  k₁ := output t
  Γ _ := Bool
  Λ := Label q t
  main := .headerStart 0
  σ := State
  initialState := (((), ()), none)
  m := program q t

end

end MaxCutGames.Explicit.MachineProductProgram

/-! Concrete header and initialized work-tape frames for the product machine. -/

namespace MaxCutGames.Explicit.MachineProductHeaders

open Turing
open MaxCutGames.Foundations Target Complexity Hastad
open MachineProductProgram

/-- All permanent input fields and fixed Horner digits are explicit tape words.
The argument is the forward-order emitted already emitted. -/
def frame {q : Nat} (H : Instance q) (t : Nat) (emitted : List Bool) : Tape t → List Bool
  | .formula => encodeWords (ProductMachineSemantics.inputTable H)
  | .extra (.inl i) =>
      if i = 0 then encodeWord H.vertices
      else if i = 7 then encodeWord q
      else if i = 8 then encodeWord H.constraints.length
      else if i = 6 then emitted.reverse else []
  | .extra (.inr i) => encodeWord (MachineProductPower.digits i.val)
  | _ => []

def headerBits {q : Nat} (H : Instance q) (t : Nat) : List Bool :=
  encodeWords [H.vertices ^ t, q ^ t, H.constraints.length ^ t]

/-- Canonical frame before the odometer digits are filled. -/
def baseTapes {q : Nat} (H : Instance q) (t : Nat) : Tape t → List Bool :=
  frame H t (headerBits H t)

@[simp] theorem frame_accumulator {q : Nat} (H : Instance q) (t : Nat) (emitted : List Bool) :
    frame H t emitted (accumulator t) = emitted.reverse := by simp [frame, accumulator, auxiliary]

@[simp] theorem frame_output {q : Nat} (H : Instance q) (t : Nat) (emitted : List Bool) :
    frame H t emitted (output t) = [] := by simp [frame, output, auxiliary]

@[simp] theorem frame_radix {q : Nat} (H : Instance q) (t : Nat) (emitted : List Bool)
    (edgeCount : Bool) :
    frame H t emitted (powerSlots t edgeCount (.inl 0)) =
      encodeWord (if edgeCount then H.constraints.length else H.vertices) := by
  cases edgeCount <;> simp [frame, powerSlots, powerRole, auxiliary]

@[simp] theorem frame_digit {q : Nat} (H : Instance q) (t : Nat) (emitted : List Bool)
    (edgeCount : Bool) (i : Fin (t + 1)) :
    frame H t emitted (powerSlots t edgeCount (.inr i)) =
      encodeWord (MachineProductPower.digits i.val) := rfl

theorem power_outside (t : Nat) (edgeCount : Bool) (i : MachineHorner.Layout (t + 1)) :
    accumulator t ≠ powerSlots t edgeCount i := by
  cases i with
  | inl i => fin_cases i <;> cases edgeCount <;> simp [accumulator, powerSlots, powerRole, auxiliary]
  | inr i => simp [accumulator, powerSlots, powerRole, auxiliary, constantDigit]

theorem frame_power_clean {q : Nat} (H : Instance q) (t : Nat) (emitted : List Bool)
    (edgeCount : Bool) : MachineHorner.Clean (powerSlots t edgeCount) (frame H t emitted) := by
  constructor <;> simp [frame, powerSlots, powerRole, auxiliary]

@[simp] theorem frame_power_output {q : Nat} (H : Instance q) (t : Nat) (emitted : List Bool)
    (edgeCount : Bool) : frame H t emitted (powerSlots t edgeCount (.inl 3)) = [] := by
  simp [frame, powerSlots, powerRole, auxiliary]

theorem frame_append {q : Nat} (H : Instance q) (t : Nat) (emitted suffix : List Bool) :
    Function.update (frame H t emitted) (accumulator t)
      (suffix.reverse ++ frame H t emitted (accumulator t)) = frame H t (emitted ++ suffix) := by
  funext tape
  cases tape <;> simp [frame, accumulator, auxiliary, Function.update_apply]
  rename_i extra
  cases extra with
  | inl i =>
    fin_cases i <;> simp []
  | inr i => simp []

/-- The generic odometer initializer has exactly the scheduler's concrete digit
frame; all permanent headers and output-emitted bits retain their identity. -/
theorem initialized_eq {q : Nat} (H : Instance q) (t : Nat) :
    MachineOdometerInit.stageTapes (initRole t) H.constraints.length (baseTapes H t) t =
      SourceOdometerSchedule.setDigits H.constraints.length (fun _ : Fin t => 0) (baseTapes H t) := by
  funext tape
  cases tape with
  | current i =>
    have h := MachineOdometerInit.output_current (initRole t) (initRole_injective t)
      H.constraints.length (baseTapes H t) i
    simpa [initRole, SourceOdometerSchedule.setDigits, i.isLt] using h
  | remaining i =>
    have h := MachineOdometerInit.output_remaining (initRole t) (initRole_injective t)
      H.constraints.length (baseTapes H t) i
    simpa [initRole, SourceOdometerSchedule.setDigits, i.isLt] using h
  | _ =>
    rw [MachineOdometerInit.stageTapes_frame (initRole t) H.constraints.length
      (baseTapes H t) t _ (fun _ => by simp [initRole]) (fun _ => by simp [initRole])]
    rfl

end MaxCutGames.Explicit.MachineProductHeaders

/-! Three actual header reads for the fixed-alphabet, fixed-power product
machine. The constraint table stays in its original order on the formula tape. -/

namespace MaxCutGames.Explicit.MachineProductHeadersRead

open Turing
open MaxCutGames.Foundations MaxCutGames.Foundations.Complexity
open MaxCutGames.Foundations.Hastad
open MachineProductProgram

noncomputable section

def inputTapes (t : Nat) (bits : List Bool) : Tape t → List Bool
  | .formula => bits
  | _ => []

def afterVertices (t n : Nat) (rest : List Bool) : Tape t → List Bool
  | .formula => rest
  | .extra (.inl i) => if i = 0 then encodeWord n else []
  | _ => []

def afterAlphabet (t n q : Nat) (rest : List Bool) : Tape t → List Bool
  | .formula => rest
  | .extra (.inl i) => if i = 0 then encodeWord n else if i = 7 then encodeWord q else []
  | _ => []

def rawResultTapes (t n q m : Nat) (body : List Bool) : Tape t → List Bool
  | .formula => body
  | .extra (.inl i) => if i = 0 then encodeWord n else if i = 7 then encodeWord q
      else if i = 8 then encodeWord m else []
  | _ => []

def resultTapes {q : Nat} (H : Target.Instance q) (t : Nat) : Tape t → List Bool
  | .formula => encodeWords (ProductMachineSemantics.inputTable H)
  | .extra (.inl i) => if i = 0 then encodeWord H.vertices else if i = 7 then encodeWord q
      else if i = 8 then encodeWord H.constraints.length else []
  | _ => []

theorem initList_eq (q t : Nat) (bits : List Bool) :
    initList (machine q t) bits =
      ⟨some (.headerStart 0), (((), ()), none), inputTapes t bits⟩ := by
  unfold initList
  congr 1
  funext k
  (cases k <;> simp [inputTapes, machine]); rfl

theorem first_result (t n : Nat) (rest : List Bool) :
    SourceMachine.fieldTapes (SourceContextLoad.Tape.formula : Tape t) (auxiliary t 0)
      (inputTapes t (encodeWord n ++ rest)) rest
      (encodeWord n ++ inputTapes t (encodeWord n ++ rest) (auxiliary t 0)) =
      afterVertices t n rest := by
  funext k
  cases k with
  | extra x =>
    cases x with
    | inl i => fin_cases i <;> simp [SourceMachine.fieldTapes, inputTapes, afterVertices, auxiliary]
    | inr i => simp [SourceMachine.fieldTapes, inputTapes, afterVertices, auxiliary]
  | _ => simp [SourceMachine.fieldTapes, inputTapes, afterVertices, auxiliary]

theorem second_result (t n q : Nat) (rest : List Bool) :
    SourceMachine.fieldTapes (SourceContextLoad.Tape.formula : Tape t) (auxiliary t 7)
      (afterVertices t n (encodeWord q ++ rest)) rest
      (encodeWord q ++ afterVertices t n (encodeWord q ++ rest) (auxiliary t 7)) =
      afterAlphabet t n q rest := by
  funext k
  cases k with
  | extra x =>
    cases x with
    | inl i => fin_cases i <;> simp [SourceMachine.fieldTapes, afterVertices, afterAlphabet, auxiliary]
    | inr i => simp [SourceMachine.fieldTapes, afterVertices, afterAlphabet, auxiliary]
  | _ => simp [SourceMachine.fieldTapes, afterVertices, afterAlphabet, auxiliary]

theorem third_result (t n q m : Nat) (body : List Bool) :
    SourceMachine.fieldTapes (SourceContextLoad.Tape.formula : Tape t) (auxiliary t 8)
      (afterAlphabet t n q (encodeWord m ++ body)) body
      (encodeWord m ++ afterAlphabet t n q (encodeWord m ++ body) (auxiliary t 8)) =
      rawResultTapes t n q m body := by
  funext k
  cases k with
  | extra x =>
    cases x with
    | inl i => fin_cases i <;> simp [SourceMachine.fieldTapes, afterAlphabet, rawResultTapes, auxiliary]
    | inr i => simp [SourceMachine.fieldTapes, afterAlphabet, rawResultTapes, auxiliary]
  | _ => simp [SourceMachine.fieldTapes, afterAlphabet, rawResultTapes, auxiliary]

def rawHeadersInTime (q t n m : Nat) (body : List Bool) :
    StateTransition.EvalsToInTime (machine q t).step
      (initList (machine q t) (encodeWords [n, q, m] ++ body))
      (some ⟨some .seedStart, (((), ()), none), rawResultTapes t n q m body⟩)
      (n + q + m + 6) := by
  have first := SourceMachine.fieldInTime
    (SourceContextLoad.Tape.formula : Tape t) (auxiliary t 0) (by simp [auxiliary])
    (.headerStart 0 : Label q t) (.headerRead 0) (some (.headerStart 1))
    (program q t) rfl rfl
    (inputTapes t (encodeWord n ++ (encodeWord q ++ (encodeWord m ++ body)))) n
    (encodeWord q ++ (encodeWord m ++ body)) rfl ((), ()) none
  rw [first_result] at first
  have second := SourceMachine.fieldInTime
    (SourceContextLoad.Tape.formula : Tape t) (auxiliary t 7) (by simp [auxiliary])
    (.headerStart 1 : Label q t) (.headerRead 1) (some (.headerStart 2))
    (program q t) rfl rfl (afterVertices t n (encodeWord q ++ (encodeWord m ++ body))) q
    (encodeWord m ++ body) rfl ((), ()) none
  rw [second_result] at second
  have third := SourceMachine.fieldInTime
    (SourceContextLoad.Tape.formula : Tape t) (auxiliary t 8) (by simp [auxiliary])
    (.headerStart 2 : Label q t) (.headerRead 2) (some .seedStart)
    (program q t) rfl rfl (afterAlphabet t n q (encodeWord m ++ body)) m body rfl ((), ()) none
  rw [third_result] at third
  have firstSecond := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ first second
  have whole := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ firstSecond third
  rw [initList_eq]
  have timed : StateTransition.EvalsToInTime (TM2.step (program q t))
      ⟨some (.headerStart 0), (((), ()), none),
        inputTapes t (encodeWord n ++ (encodeWord q ++ (encodeWord m ++ body)))⟩
      (some ⟨some .seedStart, (((), ()), none), rawResultTapes t n q m body⟩)
      (n + q + m + 6) := {
    toEvalsTo := whole.toEvalsTo
    steps_le_m := by have bound := whole.steps_le_m; omega
  }
  simpa only [FinTM2.step, FinTM2.Cfg, machine, encodeWords,
    List.nil_append, List.append_assoc] using! timed

/-- The exact runtime machine starts on the complete ordinary target game codec
and reaches the seed phase with its untouched row table and three unary headers. -/
def headersInTime {q : Nat} (H : Target.Instance q) (t : Nat) :
    StateTransition.EvalsToInTime (machine q t).step
      (initList (machine q t) (gameBits H))
      (some ⟨some .seedStart, (((), ()), none), resultTapes H t⟩)
      (H.vertices + q + H.constraints.length + 6) := by
  have input : gameBits H = encodeWords [H.vertices, q, H.constraints.length] ++
      encodeWords (ProductMachineSemantics.inputTable H) := by
    simp only [gameBits, gameWords, ProductMachineSemantics.inputTable, encodeWords_append]
  have result : rawResultTapes t H.vertices q H.constraints.length
      (encodeWords (ProductMachineSemantics.inputTable H)) = resultTapes H t := rfl
  rw [input]
  simpa only [result] using rawHeadersInTime q t H.vertices H.constraints.length
    (encodeWords (ProductMachineSemantics.inputTable H))

theorem headers_budget {q : Nat} (H : Target.Instance q) (_t : Nat) :
    H.vertices + q + H.constraints.length + 6 ≤ (gameBits H).length + 3 := by
  simp [gameBits, gameWords, List.length_append, encodeWords]
  omega

end
end MaxCutGames.Explicit.MachineProductHeadersRead

/-! Actual literal initialization of the finitely many product power digits. -/

namespace MaxCutGames.Explicit.MachineProductHeaders

open Turing
open MaxCutGames.Foundations Target Complexity Hastad
open MachineProductProgram

noncomputable section

theorem seedCommands_nodup (t : Nat) : ((seedCommands t).map Prod.fst).Nodup := by
  simp only [seedCommands, List.map_ofFn, Function.comp_def]
  apply List.nodup_ofFn.mpr
  intro i j same
  simpa [constantDigit] using same

theorem seed_result {q : Nat} (H : Instance q) (t : Nat) :
    MachineProductSeed.finalTapes (seedCommands t)
      (MachineProductHeadersRead.resultTapes H t) = frame H t [] := by
  have unchanged (tape : Tape t) (outside : ∀ i, tape ≠ constantDigit t i) :
      MachineProductSeed.finalTapes (seedCommands t)
        (MachineProductHeadersRead.resultTapes H t) tape =
        MachineProductHeadersRead.resultTapes H t tape := by
    apply MachineProductSeed.finalTapes_frame
    intro command member
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp member
    exact outside i
  funext tape
  cases tape with
  | extra extra =>
    cases extra with
    | inl i =>
      rw [unchanged _ (by intro j; simp [constantDigit])]
      fin_cases i <;> simp [MachineProductHeadersRead.resultTapes, frame]
    | inr i =>
      have run := MachineProductSeed.finalTapes_field (seedCommands t) (seedCommands_nodup t)
        (MachineProductHeadersRead.resultTapes H t)
        (constantDigit t i, encodeWord (MachineProductPower.digits i.val))
        (by apply List.mem_ofFn.mpr; exact ⟨i, rfl⟩)
      simpa [constantDigit, MachineProductHeadersRead.resultTapes, frame] using run
  | _ =>
    rw [unchanged _ (by intro j; simp [constantDigit])]
    rfl

def seedBridge {q : Nat} (H : Instance q) (t : Nat) :
    StateTransition.EvalsToInTime (machine q t).step
      ⟨some .seedStart, (((), ()), none), MachineProductHeadersRead.resultTapes H t⟩
      (some ⟨MachineProductSeed.entry (seedCommands t) Label.seed
        (some (.power false (.inl .start))), (((), ()), none),
        MachineProductHeadersRead.resultTapes H t⟩) 1 where
  steps := 1
  evals_in_steps := by
    change some (TM2.stepAux (program q t .seedStart) _ _) =
      some (⟨MachineProductSeed.entry (seedCommands t) Label.seed
        (some (.power false (.inl .start))), (((), ()), none),
        MachineProductHeadersRead.resultTapes H t⟩ : TM2.Cfg (fun _ : Tape t => Bool) (Label q t) State)
    simp only [program]
    cases MachineProductSeed.entry (seedCommands t) (Label.seed (q := q))
      (some (.power false (.inl .start))) <;> rfl
  steps_le_m := Nat.le_refl _

def seedInTime {q : Nat} (H : Instance q) (t : Nat) :
    StateTransition.EvalsToInTime (machine q t).step
      ⟨some .seedStart, (((), ()), none), MachineProductHeadersRead.resultTapes H t⟩
      (some ⟨some (.power false (.inl .start)), (((), ()), none), frame H t []⟩)
      (t + 2) := by
  have trace := MachineProductSeed.seedTrace (seedCommands t) (Label.seed (q := q))
    (some (.power false (.inl .start))) (program q t) (fun _ => rfl)
    (MachineProductHeadersRead.resultTapes H t) ((), ()) none
  rw [seed_result] at trace
  have seed : StateTransition.EvalsToInTime (machine q t).step
      ⟨MachineProductSeed.entry (seedCommands t) Label.seed
        (some (.power false (.inl .start))), (((), ()), none),
        MachineProductHeadersRead.resultTapes H t⟩
      (some ⟨some (.power false (.inl .start)), (((), ()), none), frame H t []⟩)
      (t + 1) := {
    steps := (seedCommands t).length
    evals_in_steps := trace
    steps_le_m := by simp [seedCommands] }
  have whole := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ (seedBridge H t) seed
  exact {
    toEvalsTo := whole.toEvalsTo
    steps_le_m := by have h := whole.steps_le_m; omega }

end
end MaxCutGames.Explicit.MachineProductHeaders

/-! The three actual output-header emissions of the product controller. -/

namespace MaxCutGames.Explicit.MachineProductHeaders

open Turing
open MaxCutGames.Foundations Target Complexity Hastad
open MachineProductProgram

noncomputable section

def powerExit (q t : Nat) (edgeCount : Bool) : Label q t :=
  if edgeCount then MachineOdometerInit.labelAt Label.initialize 0 else .alphabetHeader

def powerInTime {q : Nat} (H : Instance q) (t : Nat) (emitted : List Bool) (edgeCount : Bool) :
    StateTransition.EvalsToInTime (machine q t).step
      ⟨some (.power edgeCount (.inl .start)), (((), ()), none), frame H t emitted⟩
      (some ⟨some (powerExit q t edgeCount), (((), ()), none),
        frame H t (emitted ++ encodeWord
          ((if edgeCount then H.constraints.length else H.vertices) ^ t))⟩)
      (MachineProductPower.steps (if edgeCount then H.constraints.length else H.vertices) t) := by
  have trace := MachineProductPower.powerTrace (powerSlots t edgeCount) (accumulator t)
    (power_outside t edgeCount) (Label.power edgeCount) (some (powerExit q t edgeCount))
    (program q t) (by intro inner; cases edgeCount <;> rfl) (frame H t emitted)
    (if edgeCount then H.constraints.length else H.vertices)
    (frame_radix H t emitted edgeCount) (frame_digit H t emitted edgeCount)
    (frame_power_clean H t emitted edgeCount) (frame_power_output H t emitted edgeCount) () none
  rw [frame_append] at trace
  exact { steps := _, evals_in_steps := trace, steps_le_m := Nat.le_refl _ }

def alphabetInTime {q : Nat} (H : Instance q) (t : Nat) (emitted : List Bool) :
    StateTransition.EvalsToInTime (machine q t).step
      ⟨some .alphabetHeader, (((), ()), none), frame H t emitted⟩
      (some ⟨some (.power true (.inl .start)), (((), ()), none),
        frame H t (emitted ++ encodeWord (q ^ t))⟩) 1 := by
  have trace := MachineInitialHeaders.literalTrace (accumulator t) (encodeWord (q ^ t))
    (.alphabetHeader : Label q t) (some (.power true (.inl .start)))
    (program q t) rfl (frame H t emitted) ((), ()) none
  rw [frame_append] at trace
  exact { steps := 1, evals_in_steps := trace, steps_le_m := Nat.le_refl _ }

def powersInTime {q : Nat} (H : Instance q) (t : Nat) :
    StateTransition.EvalsToInTime (machine q t).step
      ⟨some (.power false (.inl .start)), (((), ()), none), frame H t []⟩
      (some ⟨some (MachineOdometerInit.labelAt Label.initialize 0), (((), ()), none), baseTapes H t⟩)
      (MachineProductPower.steps H.vertices t + 1 + MachineProductPower.steps H.constraints.length t) := by
  have first := powerInTime H t [] false
  have second := alphabetInTime H t (encodeWord (H.vertices ^ t))
  have third := powerInTime H t (encodeWord (H.vertices ^ t) ++ encodeWord (q ^ t)) true
  simp only [Bool.false_eq_true, ↓reduceIte, powerExit, List.nil_append] at first
  simp only [↓reduceIte, powerExit] at third
  have firstSecond := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ first second
  have whole := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ firstSecond third
  have finalFrame : frame H t
      ((encodeWord (H.vertices ^ t) ++ encodeWord (q ^ t)) ++
        encodeWord (H.constraints.length ^ t)) = baseTapes H t := by
    simp only [baseTapes, headerBits, encodeWords, List.append_nil, List.append_assoc]
  rw [finalFrame] at whole
  exact {
    toEvalsTo := whole.toEvalsTo
    steps_le_m := by have h := whole.steps_le_m; omega }

end
end MaxCutGames.Explicit.MachineProductHeaders

/-! Complete actual initialization of the independent-product machine. -/

namespace MaxCutGames.Explicit.MachineProductHeaders

open Turing
open MaxCutGames.Foundations Target Complexity Hastad
open MachineProductProgram

noncomputable section

def initializeInTime {q : Nat} (H : Instance q) (t : Nat) :
    StateTransition.EvalsToInTime (machine q t).step
      ⟨some (MachineOdometerInit.labelAt Label.initialize 0), (((), ()), none), baseTapes H t⟩
      (some (SourceOdometerSchedule.initialConfiguration (m := H.constraints.length)
        t (rowMain q t) ((), ()) (baseTapes H t)))
      (t * (2 * H.constraints.length + 6) + 1) := by
  have run := MachineOdometerInit.initializeInTime (initRole t) (initRole_injective t)
    Label.initialize (some (rowMain q t)) (program q t) (fun _ => rfl)
    H.constraints.length H.constraintCount_positive (baseTapes H t)
    (by simp [baseTapes, frame, initRole, auxiliary])
    (by intro j; rfl) (by intro j; rfl) rfl ((), ())
  rw [initialized_eq] at run
  exact run

def steps {q : Nat} (H : Instance q) (t : Nat) : Nat :=
  H.vertices + q + H.constraints.length + 6 + (t + 2) +
    (MachineProductPower.steps H.vertices t + 1 + MachineProductPower.steps H.constraints.length t) +
    (t * (2 * H.constraints.length + 6) + 1)

/-- Header reading, literal seed setup, actual Horner power computation, and
all odometer digits are supplied by real execution traces of the same program. -/
def prepareInTime {q : Nat} (H : Instance q) (t : Nat) :
    StateTransition.EvalsToInTime (machine q t).step
      (initList (machine q t) (gameBits H))
      (some (SourceOdometerSchedule.initialConfiguration (m := H.constraints.length)
        t (rowMain q t) ((), ()) (baseTapes H t))) (steps H t) := by
  have headers := MachineProductHeadersRead.headersInTime H t
  have seeds := seedInTime H t
  have powers := powersInTime H t
  have initialized := initializeInTime H t
  have first := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ headers seeds
  have second := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ first powers
  have whole := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ second initialized
  exact {
    toEvalsTo := whole.toEvalsTo
    steps_le_m := by have h := whole.steps_le_m; unfold steps; omega }

def timePolynomial (t : Nat) : Polynomial Nat :=
  Polynomial.X + 3 + Polynomial.C (t + 2) +
    Polynomial.C 2 * (MachineProductPower.timePolynomial t).comp (Polynomial.X + 1) + 1 +
    Polynomial.C t * (Polynomial.C 2 * Polynomial.X + 6) + 1

theorem steps_le {q : Nat} (H : Instance q) (t : Nat) :
    steps H t ≤ (timePolynomial t).eval (gameBits H).length := by
  have headerBound := MachineProductHeadersRead.headers_budget H t
  have hn : H.vertices ≤ (gameBits H).length + 1 := by omega
  have hm : H.constraints.length ≤ (gameBits H).length + 1 := by omega
  have hm' : H.constraints.length ≤ (gameBits H).length := by omega
  have first := MachineProductPower.steps_le H.vertices t ((gameBits H).length + 1) hn (by omega)
  have second := MachineProductPower.steps_le H.constraints.length t ((gameBits H).length + 1) hm (by omega)
  have initialization := Nat.mul_le_mul_left t (show 2 * H.constraints.length + 6 ≤
      2 * (gameBits H).length + 6 by omega)
  simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_comp,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_ofNat]
  unfold steps
  omega

/-- Polynomial initialization in the literal incoming instance-code length. -/
def inPolynomialTime {q : Nat} (H : Instance q) (t : Nat) :
    StateTransition.EvalsToInTime (machine q t).step
      (initList (machine q t) (gameBits H))
      (some (SourceOdometerSchedule.initialConfiguration (m := H.constraints.length)
        t (rowMain q t) ((), ()) (baseTapes H t)))
      ((timePolynomial t).eval (gameBits H).length) :=
  { toEvalsTo := (prepareInTime H t).toEvalsTo
    steps_le_m := (prepareInTime H t).steps_le_m.trans (steps_le H t) }

end
end MaxCutGames.Explicit.MachineProductHeaders

/-! Polynomial bounds for actual field and row traces. The output accumulator
is excluded from local cleanup and is never rescanned by row emission. -/

namespace MaxCutGames.Explicit.MachineProductBounds

open MaxCutGames.Foundations.Complexity

variable {K : Type} [DecidableEq K] {width : Nat}

noncomputable def fieldPolynomial (width : Nat) : Polynomial Nat :=
  Polynomial.C width * (7 * Polynomial.X + 6) + 1 +
    MachineHorner.timePolynomial width + (Polynomial.X + 1) ^ width + 2 +
    Polynomial.C (width + 2) * (Polynomial.C width * (Polynomial.X + 1) + 1)

@[simp] theorem fieldPolynomial_eval (width magnitude : Nat) :
    (fieldPolynomial width).eval magnitude =
      width * (7 * magnitude + 6) + 1 + (MachineHorner.timePolynomial width).eval magnitude +
        (magnitude + 1) ^ width + 2 + (width + 2) * (width * (magnitude + 1) + 1) := by
  simp [fieldPolynomial]

theorem field_steps_le (slots : MachineProductField.Layout width ↪ K) (table : List Nat)
    (coefficient : Nat) (indices offsets fields : Fin width → Nat)
    (selected : ∀ i, table[coefficient * indices i + offsets i]? = some (fields i))
    (base : K → List Bool) (ready : MachineProductField.Ready slots base)
    (radix : Nat) (digits : Nat → Nat) (magnitude : Nat)
    (tableBound : (encodeWords table).length ≤ magnitude)
    (indexBound : ∀ i, indices i ≤ magnitude) (radixBound : radix ≤ magnitude)
    (digitBound : ∀ i, i < width → digits i ≤ magnitude) :
    MachineProductField.steps slots table coefficient indices offsets fields base radix digits ≤
      (fieldPolynomial width).eval magnitude := by
  have gather := MachineProductGather.steps_le table coefficient width magnitude indices offsets fields selected indexBound
  have horner := MachineHorner.steps_le_timePolynomial radix digits width magnitude radixBound digitBound
  have value := MachineHorner.value_le radix digits width magnitude radixBound digitBound width (Nat.le_refl _)
  have cleanup := MachineProductField.cleanup_steps_le slots table coefficient indices offsets fields selected
    base ready (MachineHorner.value radix digits width)
  have gatherBound : width * (2 * magnitude + 5 * (encodeWords table).length + 6) + 1 ≤
      width * (7 * magnitude + 6) + 1 := by gcongr; omega
  have cleanupBound : (width + 2) * (width * ((encodeWords table).length + 1) + 1) ≤
      (width + 2) * (width * (magnitude + 1) + 1) := by gcongr
  rw [fieldPolynomial_eval]
  unfold MachineProductField.steps
  omega

def rowCost (slots : MachineProductRow.Layout width ↪ K) (table : List Nat) (coefficient : Nat)
    (indices : Fin width → Nat) (radices : Bool → Nat)
    (fields : MachineProductRow.Command width → Fin width → Nat)
    (digits : MachineProductRow.Command width → Nat → Nat)
    (c : MachineProductRow.Command width) (base : K → List Bool) : Nat :=
  MachineProductField.steps (MachineProductRow.fieldSlots slots c.1) table coefficient indices c.2
    (fields c) base (radices c.1) (digits c)

theorem row_steps_le (slots : MachineProductRow.Layout width ↪ K) (table : List Nat)
    (coefficient : Nat) (indices : Fin width → Nat) (radices : Bool → Nat)
    (commands : List (MachineProductRow.Command width))
    (fields : MachineProductRow.Command width → Fin width → Nat)
    (digits : MachineProductRow.Command width → Nat → Nat)
    (selected : ∀ c ∈ commands, ∀ i, table[coefficient * indices i + c.2 i]? = some (fields c i))
    (base : K → List Bool) (ready : MachineProductRow.Ready slots table indices radices base)
    (magnitude : Nat) (tableBound : (encodeWords table).length ≤ magnitude)
    (indexBound : ∀ i, indices i ≤ magnitude) (radixBound : ∀ b, radices b ≤ magnitude)
    (digitBound : ∀ c ∈ commands, ∀ i, i < width → digits c i ≤ magnitude) :
    MachineFiniteSequence.steps
      (MachineProductRow.result slots (fun c => MachineHorner.value (radices c.1) (digits c) width))
      (rowCost slots table coefficient indices radices fields digits) commands base ≤
      commands.length * (fieldPolynomial width).eval magnitude := by
  induction commands generalizing base with
  | nil => simp [MachineFiniteSequence.steps]
  | cons command commands ih =>
    have first := field_steps_le (MachineProductRow.fieldSlots slots command.1) table coefficient
      indices command.2 (fields command) (selected command (by simp)) base (ready.work command.1)
      (radices command.1) (digits command) magnitude tableBound indexBound (radixBound command.1)
      (digitBound command (by simp))
    have nextReady := MachineProductRow.Ready.appendField slots table indices radices base ready
      (MachineHorner.value (radices command.1) (digits command) width)
    have rest := ih (fun c hc => selected c (by simp [hc]))
      (MachineProductRow.result slots (fun c => MachineHorner.value (radices c.1) (digits c) width)
        command base) nextReady (fun c hc => digitBound c (by simp [hc]))
    rw [MachineFiniteSequence.steps, List.length_cons, Nat.add_mul, Nat.one_mul]
    simpa only [Nat.add_comm, rowCost] using Nat.add_le_add first rest

end MaxCutGames.Explicit.MachineProductBounds

end OAI
