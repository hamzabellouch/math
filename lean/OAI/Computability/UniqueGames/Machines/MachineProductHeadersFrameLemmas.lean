import OAI.Computability.UniqueGames.Machines.MachineProductFieldLemmas
import OAI.Computability.UniqueGames.Machines.MachineProductProgram

namespace OAI


/-! Concrete header and initialized work-tape frames for the product machine. -/

namespace UniqueGamesTheorem.Explicit.MachineProductHeaders

open Turing
open UniqueGamesTheorem.Foundations Target Complexity Hastad
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
    fin_cases i <;> simp
  | inr i => simp

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




/-! The three actual output-header emissions of the product controller. -/




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
end UniqueGamesTheorem.Explicit.MachineProductHeaders



/-! Three actual header reads for the fixed-alphabet, fixed-power product
machine. The constraint table stays in its original order on the formula tape. -/

namespace UniqueGamesTheorem.Explicit.MachineProductHeadersRead


open Turing
open UniqueGamesTheorem.Foundations UniqueGamesTheorem.Foundations.Complexity
open UniqueGamesTheorem.Foundations.Hastad
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

theorem headers_budget {q : Nat} (H : Target.Instance q) (_power : Nat) :
    H.vertices + q + H.constraints.length + 6 ≤ (gameBits H).length + 3 := by
  simp [gameBits, gameWords, List.length_append, encodeWords]
  omega

end
end UniqueGamesTheorem.Explicit.MachineProductHeadersRead



/-! Actual literal initialization of the finitely many product power digits. -/

namespace UniqueGamesTheorem.Explicit.MachineProductHeaders

open Turing
open UniqueGamesTheorem.Foundations Target Complexity Hastad
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
    change some (TM2.stepAux (program q t .seedStart) _ _) = _
    simp only [program]
    cases h : MachineProductSeed.entry (seedCommands t) (Label.seed (q := q))
      (some (.power false (.inl .start))) <;>
      simp only [Reduction.MachineTransfer.exitAt, TM2.stepAux] <;> erw [h] <;> rfl
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




/-! Complete actual initialization of the independent-product machine. -/





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
end UniqueGamesTheorem.Explicit.MachineProductHeaders



/-! Whole tuple traversal of the concrete product program. The odometer theorem
is instantiated by the proved actual row trace, not by an assumed row machine. -/

namespace UniqueGamesTheorem.Explicit.MachineProductLoop

open Turing
open UniqueGamesTheorem.Foundations
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
    encodeWords, encodeWord_length, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  omega

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

end UniqueGamesTheorem.Explicit.MachineProductLoop



/-! Exact final cleanup and binary-output identification for the product
controller. The final runtime bound is derived from actual stack lengths. -/

namespace UniqueGamesTheorem.Explicit.MachineProductFinish

open Turing
open UniqueGamesTheorem.Foundations
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
    simp only [program, UniqueGamesTheorem.Reduction.MachineTransfer.exitAt]
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

end UniqueGamesTheorem.Explicit.MachineProductFinish

end OAI
