import Mathlib
import OAI.Computability.MinUncut.Games.GraphIterationBounds
import OAI.Computability.MinUncut.Games.FinalCNFOutput

namespace OAI

namespace MinUncutGames.Foundations.Complexity.MachineTableIteration

open Turing PCP RoundTables GraphIterationBounds

def finalTable (H : BaseTable) (input : Input) : GraphTables.Table :=
  TableIteration.runTables H (count input) input.val

noncomputable def counterCertificate : TM2ComputableInPolyTime inputBits countedBits (id : Input → Input) where
  toTM2ComputableAux := GraphCounterPrefix.computableInPolyTime.toTM2ComputableAux
  time := GraphCounterPrefix.computableInPolyTime.time
  outputsFun input := GraphCounterPrefix.computableInPolyTime.outputsFun input.val

variable (H : BaseTable)
  (body : TM2ComputableInPolyTime GraphTables.tableBits GraphTables.tableBits (build H))

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

noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime inputBits GraphTables.tableBits (finalTable H) :=
  MachineSequential.composeBits counterCertificate (countedCertificate H body)

noncomputable def initialCertificate :
    TM2ComputableInPolyTime formulaBits inputBits initial where
  toTM2ComputableAux := MachineRawInitialTable.computableInPolyTime.toTM2ComputableAux
  time := MachineRawInitialTable.computableInPolyTime.time
  outputsFun F := MachineRawInitialTable.computableInPolyTime.outputsFun F

noncomputable def tableCertificate :
    TM2ComputableInPolyTime formulaBits GraphTables.tableBits (TableIteration.outputTable H) := by
  change TM2ComputableInPolyTime formulaBits GraphTables.tableBits
    (fun F => finalTable H (initial F))
  exact MachineSequential.composeBits (f := initial) (g := finalTable H)
    initialCertificate (computableInPolyTime H body)

noncomputable def gapMapCertificate :
    TM2ComputableInPolyTime formulaBits formulaBits (TableIteration.gapMap H) :=
  MachineSequential.composeBits (f := TableIteration.outputTable H) (g := FinalTableFormula.output)
    (tableCertificate H body)
    FinalCNFMachine.Program.computableInPolyTime

end MinUncutGames.Foundations.Complexity.MachineTableIteration

namespace MinUncutGames.Foundations.Complexity.TableIterationFiniteAlphabet

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

end MinUncutGames.Foundations.Complexity.TableIterationFiniteAlphabet

end OAI
