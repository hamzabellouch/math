import Mathlib.Tactic.Ring
import OAI.Computability.UniqueGames.Machines.GraphCounterStartLemmas
import OAI.Computability.UniqueGames.Machines.MachineFiniteAlphabet
import OAI.Computability.UniqueGames.Machines.MachineLazyTableRuntime
import OAI.Computability.UniqueGames.Machines.MachinePaddedOverlayRuntimeLemmas
import OAI.Computability.UniqueGames.Machines.MachineRegularTableBoundsLemmas
import OAI.Computability.UniqueGames.Machines.PoweringPolynomialBudgetLemmas
import OAI.Computability.UniqueGames.PCP.Body
import OAI.Computability.UniqueGames.PCP.DriverLemmas
import OAI.Computability.UniqueGames.PCP.Initialization
import OAI.Computability.UniqueGames.PCP.LoopState
import OAI.Computability.UniqueGames.PCP.RawInitialTablesLemmas

namespace OAI


/-!
The concrete tapes produced by initialization satisfy the row-zero loop
invariant. Execution of initialization is proved separately by
`Initialization.initializeInTime`; this bridge identifies its resulting tapes.
-/

namespace UniqueGamesTheorem.Foundations.PCP.AlphabetTable.LoopInitialization

open UniqueGamesTheorem.Foundations.Complexity
open RuntimeModel LoopState

/-- The actual initial loop tapes contain the complete unread input rows and
exactly the two output headers in reverse order on the accumulation tape. -/
theorem initialization_ready {q : Nat} (input : GenericGraphTables.Table q) :
    Ready input 0 (Initialization.loopTapes input) where
  le_darts := Nat.zero_le _
  original := rfl
  cursor := by
    change Initialization.rowsBits input = cursorBits input 0
    rw [cursorBits_zero]
    rfl
  vertices := rfl
  darts := rfl
  counter := by simp [Initialization.loopTapes]
  edge := rfl
  tail := rfl
  reverseIndex := rfl
  head := rfl
  scratch := rfl
  compareLeft := rfl
  compareRight := rfl
  output := rfl
  reversed := by
    change (Initialization.headerBits input).reverse = (prefixBits input 0).reverse
    rw [prefixBits_zero]
    rfl

end UniqueGamesTheorem.Foundations.PCP.AlphabetTable.LoopInitialization



namespace UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Loop


open Turing
open UniqueGamesTheorem.Foundations.Complexity
open RuntimeModel

variable {q : Nat}

/-- The zero guard preserves all tapes, resets its temporary register, and
enters the actual driver's output-reversal phase in one transition. -/
def zeroGuardInTime (input : GenericGraphTables.Table q) (base : Tape → List Bool)
    (ready : LoopState.Ready input input.darts base)
    (relation : GenericGraphTables.RelationTable q) (flag : Bool) :
    StateTransition.EvalsToInTime (TM2.step (Driver.program q))
      ⟨some .guard, normal relation flag, base⟩
      (some ⟨some .reverseOutput, normal relation flag, base⟩) 1 := by
  have counterSelf : MachineUnaryCounter.counterTapes Tape.counter base 0 [] = base := by
    simp only [MachineUnaryCounter.counterTapes, List.append_nil,
      ← ready.counter_at_end, Function.update_eq_self]
  have run := MachineUnaryCounter.guardInTime_zero Tape.counter
    (Driver.Label.guard : Driver.Label q) .tailStart .reverseOutput
    (Driver.program q) (Driver.program_guard q) base [] (normal relation flag).1 none
  simpa only [counterSelf, normal] using run

/-- Concrete final configuration and full remaining-loop execution. -/
structure LoopResult (input : GenericGraphTables.Table q) (e remaining : Nat)
    (base : Tape → List Bool) (oldRelation : GenericGraphTables.RelationTable q)
    (oldFlag : Bool) where
  tapes : Tape → List Bool
  relation : GenericGraphTables.RelationTable q
  flag : Bool
  ready : LoopState.Ready input input.darts tapes
  run : StateTransition.EvalsToInTime (TM2.step (Driver.program q))
    ⟨some .guard, normal oldRelation oldFlag, base⟩
    (some ⟨some .reverseOutput, normal relation flag, tapes⟩)
    (remaining * Body.bodyTime q (LoopState.inputBits input).length + 1)

def runRemaining (input : GenericGraphTables.Table q) :
    (remaining e : Nat) → e + remaining = input.darts →
    (base : Tape → List Bool) → LoopState.Ready input e base →
    (oldRelation : GenericGraphTables.RelationTable q) → (oldFlag : Bool) →
      LoopResult input e remaining base oldRelation oldFlag
  | 0, e, finished, base, ready, oldRelation, oldFlag => by
    have atEnd : e = input.darts := by omega
    subst e
    exact {
      tapes := base
      relation := oldRelation
      flag := oldFlag
      ready := ready
      run := by
        simpa only [Nat.zero_mul, Nat.zero_add] using
          zeroGuardInTime input base ready oldRelation oldFlag }
  | remaining + 1, e, finished, base, ready, oldRelation, oldFlag => by
    have beforeEnd : e < input.darts := by omega
    let edge : Fin input.darts := ⟨e, beforeEnd⟩
    let one := Body.rowStep input edge base ready oldRelation oldFlag
    let rest := runRemaining input remaining (e + 1) (by omega) one.tapes one.ready
      input.rows[edge].relation (CompareLoop.rowLoop input edge)
    let composed := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ one.run rest.run
    refine {
      tapes := rest.tapes
      relation := rest.relation
      flag := rest.flag
      ready := rest.ready
      run := { toEvalsTo := composed.toEvalsTo, steps_le_m := ?_ } }
    have budget := composed.steps_le_m
    simpa only [Nat.succ_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using budget

/-- A quadratic prefix allowance because the number of original rows is at
most the length of their fully encoded input table. -/
def prefixTime (q N : Nat) : Nat :=
  Initialization.time N + N * Body.bodyTime q N + 1

-- Preserve the concrete run-size contribution in the derived PrefixResult instance.
private noncomputable local instance prefixRunSizeOf (input : GenericGraphTables.Table q)
    (tapes : Tape → List Bool) (relation : GenericGraphTables.RelationTable q) (flag : Bool) :
    SizeOf (StateTransition.EvalsToInTime (TM2.step (Driver.program q))
      (initList (Driver.machine q) (GenericGraphTables.tableBits input))
      (some ⟨some .reverseOutput, normal relation flag, tapes⟩)
      (prefixTime q (LoopState.inputBits input).length)) :=
  @StateTransition.EvalsToInTime._sizeOf_inst
    (TM2.Cfg Alphabet (Driver.Label q) (State q))
    (TM2.step (Driver.program q))
    (initList (Driver.machine q) (GenericGraphTables.tableBits input))
    (some ⟨some .reverseOutput, normal relation flag, tapes⟩)
    (prefixTime q (LoopState.inputBits input).length) inferInstance

/-- Actual initialization followed by every row, ending just before reversal. -/
structure PrefixResult (input : GenericGraphTables.Table q) where
  tapes : Tape → List Bool
  relation : GenericGraphTables.RelationTable q
  flag : Bool
  ready : LoopState.Ready input input.darts tapes
  run : StateTransition.EvalsToInTime (TM2.step (Driver.program q))
    (initList (Driver.machine q) (GenericGraphTables.tableBits input))
    (some ⟨some .reverseOutput, normal relation flag, tapes⟩)
    (prefixTime q (LoopState.inputBits input).length)

/-- No initialization or row trace is assumed: both are instantiated at this
actual finite driver and this input, then composed. -/
def runPrefix (input : GenericGraphTables.Table q) : PrefixResult input := by
  let rows := runRemaining input input.darts 0 (by simp)
    (Initialization.loopTapes input) (LoopInitialization.initialization_ready input)
    (Vector.replicate (q * q) false) false
  let composed := StateTransition.EvalsToInTime.trans _ _ _ _ _ _
    (Initialization.initializeInTime input) rows.run
  refine {
    tapes := rows.tapes
    relation := rows.relation
    flag := rows.flag
    ready := rows.ready
    run := { toEvalsTo := composed.toEvalsTo, steps_le_m := ?_ } }
  have budget := composed.steps_le_m
  change composed.steps ≤
    input.darts * Body.bodyTime q (LoopState.inputBits input).length + 1 +
      Initialization.time (LoopState.inputBits input).length at budget
  have rowCount : input.darts ≤ (LoopState.inputBits input).length :=
    GenericGraphTables.darts_le_tableBits_length input
  have rowBudget := Nat.mul_le_mul_right (Body.bodyTime q (LoopState.inputBits input).length)
    rowCount
  unfold prefixTime
  omega

theorem PrefixResult.reversed {input : GenericGraphTables.Table q} (result : PrefixResult input) :
    result.tapes .reversed = (GraphTables.tableBits (Table.build input)).reverse :=
  result.ready.reversed_at_end

theorem PrefixResult.output {input : GenericGraphTables.Table q} (result : PrefixResult input) :
    result.tapes .output = [] := result.ready.output

end UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Loop



namespace UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Runtime

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open RuntimeModel


noncomputable def prefixPolynomial (q : Nat) : Polynomial Nat :=
  Polynomial.C 27 * Polynomial.X + Polynomial.C 54 +
    Polynomial.X *
      (Polynomial.C (32 + 8 * (Enumeration.localCount q * (6 * (2 * 4104)))) *
        (Polynomial.X + Polynomial.C 1)) + Polynomial.C 1

theorem prefixPolynomial_eval (q N : Nat) :
    (prefixPolynomial q).eval N = Loop.prefixTime q N := by
  simp only [prefixPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, Loop.prefixTime,
    Initialization.time, Body.bodyTime]
  ring

noncomputable def time (q : Nat) : Polynomial Nat :=
  Finish.completedPolynomial q (prefixPolynomial q)

/-- The concrete driver outputs exactly the checked table encoding. -/
noncomputable def tableOutputsInTime {q : Nat} (input : GenericGraphTables.Table q) :
    TM2OutputsInTime (Driver.machine q) (GenericGraphTables.tableBits input)
      (some (GraphTables.tableBits (Table.build input)))
      ((time q).eval (GenericGraphTables.tableBits input).length) := by
  let prefixRun := Loop.runPrefix input
  have hrun : StateTransition.EvalsToInTime (Driver.machine q).step
      (initList (Driver.machine q) (GenericGraphTables.tableBits input))
      (some ⟨some .reverseOutput, normal prefixRun.relation prefixRun.flag, prefixRun.tapes⟩)
      ((prefixPolynomial q).eval (GenericGraphTables.tableBits input).length) := by
    rw [prefixPolynomial_eval]
    exact prefixRun.run
  exact Finish.finishAfterPolynomialPrefix q (GenericGraphTables.tableBits input)
    prefixRun.tapes (GraphTables.tableBits (Table.build input))
    (normal prefixRun.relation prefixRun.flag) (prefixPolynomial q) hrun
    prefixRun.ready.reversed_at_end prefixRun.ready.output

/-- Fixed q determines one finite machine and one natural polynomial. The
input and output alphabets use the exact shared Bool serialization interfaces. -/
noncomputable def tablePolynomialTime (q : Nat) :
    TM2ComputableInPolyTime (GenericGraphTables.tableBits (q := q))
      GraphTables.tableBits (Table.build (q := q)) where
  tm := Driver.machine q
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := time q
  outputsFun input := by
    change TM2OutputsInTime (Driver.machine q)
      ((GenericGraphTables.tableBits input).map id)
      (some ((GraphTables.tableBits (Table.build input)).map id))
      ((time q).eval (GenericGraphTables.tableBits input).length)
    have input_eq :
        @List.map ((Driver.machine q).Γ (Driver.machine q).k₀)
          ((Driver.machine q).Γ (Driver.machine q).k₀) id
          (GenericGraphTables.tableBits input) = GenericGraphTables.tableBits input := List.map_id _
    have output_eq :
        @List.map ((Driver.machine q).Γ (Driver.machine q).k₁)
          ((Driver.machine q).Γ (Driver.machine q).k₁) id
          (GraphTables.tableBits (Table.build input)) =
          GraphTables.tableBits (Table.build input) := List.map_id _
    simpa only [input_eq, output_eq] using tableOutputsInTime input

end UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Runtime



/-! Every work tape of the actual alphabet-table machine stores Bool symbols.
This checks the work alphabets separately from the finite-machine structure's
input-alphabet condition, without changing the runtime certificate. -/

namespace UniqueGamesTheorem.Foundations.PCP.AlphabetTable

open UniqueGamesTheorem.Foundations.Complexity

theorem Driver.finiteAlphabet (q : Nat) :
    MachineFiniteAlphabet.FiniteAlphabet (Driver.machine q) := by
  intro k
  change Finite Bool
  infer_instance

theorem Runtime.finiteAlphabet (q : Nat) :
    MachineFiniteAlphabet.FiniteAlphabet (Runtime.tablePolynomialTime q).tm :=
  Driver.finiteAlphabet q

end UniqueGamesTheorem.Foundations.PCP.AlphabetTable



/-! The actual padding, expander overlay, and lazy-loop stages composed into
one polynomial-time finite machine. The initial degree-replacement stage is
assembled separately. -/
namespace UniqueGamesTheorem.Foundations.PCP.PreprocessingFinishRuntime

open Turing UniqueGamesTheorem.Foundations.Complexity
open PreprocessingRegularTables

def finish (H : PreprocessingTables.BaseTable) (d : Nat) (input : PortTables.Input d) :
    PortTables.Input (2 * (d + internalDegree)) :=
  PreprocessingStageMaps.lazy (d + internalDegree)
    (PreprocessingStageMaps.paddedOverlay H d input)

theorem output_eq_finish (H : PreprocessingTables.BaseTable) (t : GraphTables.Table) :
    PreprocessingTables.output H t =
      finish H (internalDegree + 1) (PreprocessingStageMaps.regular H t) := rfl

theorem finish_degree_positive (d : Nat) (hd : 0 < d) : 0 < d + internalDegree :=
  hd.trans_le (Nat.le_add_right d internalDegree)

/-- Both stages supply complete executions, cleanup, and polynomial bounds;
the sequential composition includes the physical interstage bit transfer. -/
noncomputable def computableInPolyTime (H : PreprocessingTables.BaseTable)
    (d : Nat) (hd : 0 < d) :
    TM2ComputableInPolyTime (PortTables.inputBits (ports := d))
      (PortTables.inputBits (ports := 2 * (d + internalDegree))) (finish H d) := by
  change TM2ComputableInPolyTime _ _
    (fun input => PreprocessingStageMaps.lazy (d + internalDegree)
      (PreprocessingStageMaps.paddedOverlay H d input))
  exact MachineSequential.composeBits (MachinePaddedOverlayRuntime.computableInPolyTime H d hd)
    (MachineLazyTableRuntime.computableInPolyTime (d + internalDegree)
      (finish_degree_positive d hd))

theorem finite_alphabet (H : PreprocessingTables.BaseTable) (d : Nat) (hd : 0 < d) :
    MachineFiniteAlphabet.FiniteAlphabet (computableInPolyTime H d hd).tm :=
  MachineFiniteAlphabet.composeBits
    (MachinePaddedOverlayRuntime.computableInPolyTime H d hd)
    (MachineLazyTableRuntime.computableInPolyTime (d + internalDegree)
      (finish_degree_positive d hd))
    (MachinePaddedOverlayRuntime.finite_alphabet H d hd)
    (MachineLazyTableRuntime.finite_alphabet (d + internalDegree)
      (finish_degree_positive d hd))

end UniqueGamesTheorem.Foundations.PCP.PreprocessingFinishRuntime



/-! The complete actual preprocessing machine, including degree replacement,
vertex padding, explicit expander construction, overlay, and lazy edges. -/
namespace UniqueGamesTheorem.Foundations.PCP.PreprocessingRuntime
open Turing UniqueGamesTheorem.Foundations.Complexity
open PreprocessingRegularTables

noncomputable def tablePolynomialTime (H : PreprocessingTables.BaseTable) :
    TM2ComputableInPolyTime GraphTables.tableBits
      (PortTables.inputBits (ports := PreprocessingTables.degree))
      (PreprocessingTables.output H) := by
  change TM2ComputableInPolyTime GraphTables.tableBits
    (PortTables.inputBits (ports := 2 * ((internalDegree + 1) + internalDegree)))
    (fun t => PreprocessingFinishRuntime.finish H (internalDegree + 1)
      (PreprocessingStageMaps.regular H t))
  exact MachineSequential.composeBits
    (MachineRegularTableRuntime.computableInPolyTime H)
    (PreprocessingFinishRuntime.computableInPolyTime H (internalDegree + 1)
      (Nat.succ_pos internalDegree))

theorem finiteAlphabet (H : PreprocessingTables.BaseTable) :
    MachineFiniteAlphabet.FiniteAlphabet (tablePolynomialTime H).tm :=
  MachineFiniteAlphabet.composeBits
    (MachineRegularTableRuntime.computableInPolyTime H)
    (PreprocessingFinishRuntime.computableInPolyTime H (internalDegree + 1)
      (Nat.succ_pos internalDegree))
    (MachineRegularTableRuntime.finite_alphabet H)
    (PreprocessingFinishRuntime.finite_alphabet H (internalDegree + 1)
      (Nat.succ_pos internalDegree))

end UniqueGamesTheorem.Foundations.PCP.PreprocessingRuntime



/-!
Actual sequential finite-machine composition for the concrete numbered round.
The initial composition lemma isolates the preprocessing and powering execution
certificates with their shared bit codecs. The final endpoint supplies the
checked powering and alphabet machines, leaving only preprocessing explicit.
-/

namespace UniqueGamesTheorem.Foundations.PCP.RoundComputation

open Turing
open UniqueGamesTheorem.Foundations.Complexity


/-- The exact pending preprocessing interface, including its output encoding. -/
abbrev PreprocessingCertificate (H : RoundTables.BaseTable) :=
  TM2ComputableInPolyTime GraphTables.tableBits
    (PortTables.inputBits (ports := PreprocessingTables.degree))
    (PreprocessingTables.output H)

/-- The exact powering interface at the fixed parameters of the round. -/
abbrev PoweringCertificate :=
  TM2ComputableInPolyTime
    (PortTables.inputBits (ports := PreprocessingTables.degree))
    (GenericGraphTables.tableBits (q := RoundTables.alphabet))
    (PoweringTables.transform PreprocessingTables.degree RoundTables.walkParameter)

theorem powered_eq_transform (H : RoundTables.BaseTable) (table : GraphTables.Table) :
    RoundTables.powered H table =
      PoweringTables.transform PreprocessingTables.degree RoundTables.walkParameter
        (PreprocessingTables.output H table) := rfl

/-- Both actual transfer loops between the machines are included by
`MachineSequential.composeBits`; their work contributes to its polynomial. -/
noncomputable def poweredPolynomialTimeOfCertificates (H : RoundTables.BaseTable)
    (preprocessing : PreprocessingCertificate H) (powering : PoweringCertificate) :
    TM2ComputableInPolyTime GraphTables.tableBits
      (GenericGraphTables.tableBits (q := RoundTables.alphabet))
      (RoundTables.powered H) := by
  change TM2ComputableInPolyTime GraphTables.tableBits _
    (fun table => PoweringTables.transform PreprocessingTables.degree
      RoundTables.walkParameter (PreprocessingTables.output H table))
  exact MachineSequential.composeBits preprocessing powering

noncomputable def tablePolynomialTimeOfCertificates (H : RoundTables.BaseTable)
    (preprocessing : PreprocessingCertificate H) (powering : PoweringCertificate) :
    TM2ComputableInPolyTime GraphTables.tableBits GraphTables.tableBits
      (RoundTables.build H) := by
  change TM2ComputableInPolyTime GraphTables.tableBits GraphTables.tableBits
    (fun table => AlphabetTable.Table.build (RoundTables.powered H table))
  exact MachineSequential.composeBits
    (poweredPolynomialTimeOfCertificates H preprocessing powering)
    (AlphabetTable.Runtime.tablePolynomialTime RoundTables.alphabet)

/-- All intermediate work alphabets stay finite under the actual sequential
composition, provided that they are finite in the two supplied machines. -/
theorem powered_finiteAlphabet (H : RoundTables.BaseTable)
    (preprocessing : PreprocessingCertificate H) (powering : PoweringCertificate)
    (hpreprocessing : MachineFiniteAlphabet.FiniteAlphabet preprocessing.tm)
    (hpowering : MachineFiniteAlphabet.FiniteAlphabet powering.tm) :
    MachineFiniteAlphabet.FiniteAlphabet
      (poweredPolynomialTimeOfCertificates H preprocessing powering).tm :=
  MachineFiniteAlphabet.composeBits preprocessing powering hpreprocessing hpowering

/-- This is a separate work-alphabet fact about the same runtime certificate;
the final alphabet stage has homogeneous Bool tapes. -/
theorem finiteAlphabet (H : RoundTables.BaseTable)
    (preprocessing : PreprocessingCertificate H) (powering : PoweringCertificate)
    (hpreprocessing : MachineFiniteAlphabet.FiniteAlphabet preprocessing.tm)
    (hpowering : MachineFiniteAlphabet.FiniteAlphabet powering.tm) :
    MachineFiniteAlphabet.FiniteAlphabet
      (tablePolynomialTimeOfCertificates H preprocessing powering).tm :=
  MachineFiniteAlphabet.composeBits
    (poweredPolynomialTimeOfCertificates H preprocessing powering)
    (AlphabetTable.Runtime.tablePolynomialTime RoundTables.alphabet)
    (powered_finiteAlphabet H preprocessing powering hpreprocessing hpowering)
    (AlphabetTable.Runtime.finiteAlphabet RoundTables.alphabet)

/-- Powering and alphabet reduction now use their constructed finite machines.
The only remaining input is an execution certificate for preprocessing. -/
noncomputable def tablePolynomialTime (H : RoundTables.BaseTable)
    (preprocessing : PreprocessingCertificate H) :
    TM2ComputableInPolyTime GraphTables.tableBits GraphTables.tableBits
      (RoundTables.build H) :=
  tablePolynomialTimeOfCertificates H preprocessing
    (PoweringMachineRuntime.computableInPolyTime PreprocessingTables.degree
      RoundTables.walkParameter)

/-- The same certificate has finite work-tape alphabets whenever the supplied
preprocessing machine does; both later stages supply their own proof. -/
theorem tablePolynomialTime_finite_alphabet (H : RoundTables.BaseTable)
    (preprocessing : PreprocessingCertificate H)
    (hpreprocessing : MachineFiniteAlphabet.FiniteAlphabet preprocessing.tm) :
    MachineFiniteAlphabet.FiniteAlphabet
      (tablePolynomialTime H preprocessing).tm :=
  finiteAlphabet H preprocessing
    (PoweringMachineRuntime.computableInPolyTime PreprocessingTables.degree
      RoundTables.walkParameter) hpreprocessing
    (PoweringMachineRuntime.computableInPolyTime_finite_alphabet
      PreprocessingTables.degree RoundTables.walkParameter)

end UniqueGamesTheorem.Foundations.PCP.RoundComputation

end OAI
