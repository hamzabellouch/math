import OAI.Computability.UniqueGames.Machines.FinalCNFOutputLemmas
import OAI.Computability.UniqueGames.Machines.GraphCounterStartLemmas
import OAI.Computability.UniqueGames.Machines.MachineFiniteAlphabet
import OAI.Computability.UniqueGames.Machines.MachineRepeat
import OAI.Computability.UniqueGames.Machines.MachineUnaryLessAtLemmas
import OAI.Computability.UniqueGames.PCP.MachineRawInitialTable
import OAI.Computability.UniqueGames.PCP.TableIteration

namespace OAI


/-! One polynomial bounds every actual intermediate encoding in the concrete
logarithmic graph iteration. The linear recurrence is on graph size. -/

namespace UniqueGamesTheorem.Foundations.Complexity.GraphIterationBounds

open PCP RoundTables

def inputBits (input : Input) : List Bool := GraphTables.tableBits input.val

def countedBits (input : Input) : List Bool := GraphCounterPrefix.output input.val

def words (H : BaseTable) (input : Input) (i : Nat) : List Bool :=
  GraphTables.tableBits (TableIteration.runTables H i input.val)

def count (input : Input) : Nat := GraphCounterPrefix.count input.val

noncomputable def lengthPolynomial : Polynomial Nat :=
  (GraphTableComplexity.encodingPolynomial 64).comp (PCPIterationMachine.sizePolynomial sizeFactor)

theorem inputBits_le_countedBits (input : Input) : (inputBits input).length ≤ (countedBits input).length := by
  simp only [inputBits, countedBits, GraphCounterPrefix.output, List.length_append]
  omega

theorem size_le_inputBits (input : Input) : size input ≤ (inputBits input).length := by
  have h := GraphTableComplexity.size_add_two_le_bits input.val
  unfold size inputBits
  omega

theorem count_le (input : Input) : count input ≤ (countedBits input).length + 1 :=
  (PCPIterationMachine.rounds_le (size input)).trans
    (Nat.add_le_add_right ((size_le_inputBits input).trans (inputBits_le_countedBits input)) 1)

theorem intermediate_size (H : BaseTable) (input : Input) (i : Nat) (hi : i ≤ count input) :
    size (TableIteration.run H i input) ≤ PCPIterationMachine.sizeEnvelope sizeFactor (size input) := by
  apply PCPIterationMachine.semanticSize_bound
    (fun j => size (TableIteration.run H j input)) sizeFactor (size input)
    sizeFactor_positive (Nat.le_succ _) _ i hi
  intro j _
  exact step_size H (TableIteration.run H j input)

theorem intermediate_bits (H : BaseTable) (input : Input) (i : Nat) (hi : i ≤ count input) :
    (words H input i).length ≤ lengthPolynomial.eval (countedBits input).length := by
  have hsize := intermediate_size H input i hi
  have hinput := (size_le_inputBits input).trans (inputBits_le_countedBits input)
  have heval := MachineComposition.natPolynomial_eval_mono
    (PCPIterationMachine.sizePolynomial sizeFactor) hinput
  rw [PCPIterationMachine.sizePolynomial_eval, PCPIterationMachine.sizePolynomial_eval] at heval
  have hs := hsize.trans heval
  have htable : (TableIteration.runTables H i input.val).vertices +
      (TableIteration.runTables H i input.val).darts ≤
        PCPIterationMachine.sizeEnvelope sizeFactor (countedBits input).length := by
    rw [← TableIteration.run_val]
    exact hs
  rw [lengthPolynomial, Polynomial.eval_comp, PCPIterationMachine.sizePolynomial_eval]
  exact GraphTableComplexity.bits_le_of_size_le _ htable

noncomputable def runtimePolynomial (bodyTime : Polynomial Nat) : Polynomial Nat :=
  (Polynomial.X + 1) * (bodyTime.comp lengthPolynomial + 2 * lengthPolynomial + 4) +
    2 * lengthPolynomial + 4

theorem runtimePolynomial_eval (bodyTime : Polynomial Nat) (N : Nat) :
    (runtimePolynomial bodyTime).eval N =
      (N + 1) * (bodyTime.eval (lengthPolynomial.eval N) + 2 * lengthPolynomial.eval N + 4) +
        2 * lengthPolynomial.eval N + 4 := by
  simp only [runtimePolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
    Polynomial.eval_one, Polynomial.eval_ofNat, Polynomial.eval_comp]

end UniqueGamesTheorem.Foundations.Complexity.GraphIterationBounds



/-! Actual polynomial-time iteration of the concrete graph-table round. A
certificate for that one body is the only supplied machine input. Counter
preparation, repeated calls, tape handoffs, and final cleanup are all proved. -/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineTableIteration

open Turing PCP RoundTables GraphIterationBounds


def finalTable (H : BaseTable) (input : Input) : GraphTables.Table :=
  TableIteration.runTables H (count input) input.val

noncomputable def counterCertificate : TM2ComputableInPolyTime inputBits countedBits (id : Input → Input) where
  toTM2ComputableAux := GraphCounterPrefix.computableInPolyTime.toTM2ComputableAux
  time := GraphCounterPrefix.computableInPolyTime.time
  outputsFun input := GraphCounterPrefix.computableInPolyTime.outputsFun input.val

variable (H : BaseTable)
  (body : TM2ComputableInPolyTime GraphTables.tableBits GraphTables.tableBits (build H))

/-- The generic repeat machine executes only the actual successive graph words.
Its polynomial bound uses the proved linear growth of their semantic sizes. -/
noncomputable def countedCertificate :
    TM2ComputableInPolyTime countedBits GraphTables.tableBits (finalTable H) where
  tm := MachineRepeat.machine body.tm body.inputAlphabet body.outputAlphabet
  inputAlphabet := body.inputAlphabet
  outputAlphabet := body.inputAlphabet
  time := runtimePolynomial body.time
  outputsFun input := by
    let budgets := fun i => body.time.eval (words H input i).length
    have runs (i : Nat) (_hi : i < count input) :
        TM2OutputsInTime body.tm ((words H input i).map body.inputAlphabet.symm)
          (some ((words H input (i + 1)).map body.outputAlphabet.symm)) (budgets i) := by
      exact body.outputsFun (TableIteration.runTables H i input.val)
    let run := MachineRepeat.executeSequence body.tm body.inputAlphabet body.outputAlphabet
      (count input) (words H input) budgets runs
    have start : encodeWord (count input) ++ words H input 0 = countedBits input := rfl
    have finish : words H input (count input) = GraphTables.tableBits (finalTable H input) := rfl
    rw [start, finish] at run
    refine { toEvalsTo := run.toEvalsTo, steps_le_m := ?_ }
    let N := (countedBits input).length
    let L := lengthPolynomial.eval N
    let B := body.time.eval L
    have hl (i : Nat) (hi : i ≤ count input) : (words H input i).length ≤ L :=
      intermediate_bits H input i hi
    have hb (i : Nat) (hi : i < count input) : budgets i ≤ B :=
      MachineComposition.natPolynomial_eval_mono body.time (hl i hi.le)
    have hloop := MachineRepeat.loopBudget_le (count input) (words H input) budgets B L hb hl
    have hc : count input ≤ N + 1 := count_le input
    rw [runtimePolynomial_eval]
    calc
      run.steps ≤ count input + 1 + MachineRepeat.loopBudget (count input) (words H input) budgets :=
        run.steps_le_m
      _ ≤ count input + 1 + (count input * (B + 2 * L + 3) + 2 * L + 3) :=
        Nat.add_le_add_left hloop _
      _ = count input * (B + 2 * L + 4) + 2 * L + 4 := by ring
      _ ≤ (N + 1) * (B + 2 * L + 4) + 2 * L + 4 :=
        Nat.add_le_add_right (Nat.add_le_add_right (Nat.mul_le_mul_right _ hc) _) _

/-- One actual finite machine computes the complete logarithmic iteration. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime inputBits GraphTables.tableBits (finalTable H) :=
  MachineSequential.composeBits counterCertificate (countedCertificate H body)

noncomputable def initialCertificate :
    TM2ComputableInPolyTime formulaBits inputBits initial where
  toTM2ComputableAux := MachineRawInitialTable.computableInPolyTime.toTM2ComputableAux
  time := MachineRawInitialTable.computableInPolyTime.time
  outputsFun F := MachineRawInitialTable.computableInPolyTime.outputsFun F

/-- The initial graph and entire repeated table transformation have concrete
finite-machine executions with the same formula and table encodings. -/
noncomputable def tableCertificate :
    TM2ComputableInPolyTime formulaBits GraphTables.tableBits (TableIteration.outputTable H) := by
  change TM2ComputableInPolyTime formulaBits GraphTables.tableBits
    (fun F => finalTable H (initial F))
  exact MachineSequential.composeBits (f := initial) (g := finalTable H)
    initialCertificate (computableInPolyTime H body)

/-- Actual 3SAT gap-map runtime follows from the one concrete round certificate;
initialization, variable repetition, and the final CNF converter are supplied. -/
noncomputable def gapMapCertificate :
    TM2ComputableInPolyTime formulaBits formulaBits (TableIteration.gapMap H) :=
  MachineSequential.composeBits (f := TableIteration.outputTable H) (g := FinalTableFormula.output)
    (tableCertificate H body)
    FinalCNFMachine.Program.computableInPolyTime

end UniqueGamesTheorem.Foundations.Complexity.MachineTableIteration



namespace UniqueGamesTheorem.Foundations.Complexity.TableIterationFiniteAlphabet

open PCP MachineFiniteAlphabet

theorem initial : FiniteAlphabet MachineRawInitialTable.computableInPolyTime.tm := by
  intro k
  change Finite Bool
  infer_instance

theorem finalCNF : FiniteAlphabet FinalCNFMachine.Program.computableInPolyTime.tm := by
  intro k
  change Finite Bool
  infer_instance

theorem counter : FiniteAlphabet MachineTableIteration.counterCertificate.tm := by
  intro k
  change Finite Bool
  infer_instance

variable (H : RoundTables.BaseTable)
  (body : Turing.TM2ComputableInPolyTime GraphTables.tableBits GraphTables.tableBits
    (RoundTables.build H))
  (finiteBody : FiniteAlphabet body.tm)

include finiteBody

theorem counted : FiniteAlphabet (MachineTableIteration.countedCertificate H body).tm :=
  repeat_machine body.tm body.inputAlphabet body.outputAlphabet finiteBody

theorem iteration : FiniteAlphabet (MachineTableIteration.computableInPolyTime H body).tm :=
  composeBits MachineTableIteration.counterCertificate
    (MachineTableIteration.countedCertificate H body) counter (counted H body finiteBody)

theorem table : FiniteAlphabet (MachineTableIteration.tableCertificate H body).tm :=
  composeBits MachineTableIteration.initialCertificate
    (MachineTableIteration.computableInPolyTime H body) initial (iteration H body finiteBody)

theorem gapMap : FiniteAlphabet (MachineTableIteration.gapMapCertificate H body).tm :=
  composeBits (MachineTableIteration.tableCertificate H body)
    FinalCNFMachine.Program.computableInPolyTime (table H body finiteBody) finalCNF

end UniqueGamesTheorem.Foundations.Complexity.TableIterationFiniteAlphabet

end OAI
