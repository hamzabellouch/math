import OAI.Computability.PerfectCompleteness.Foundations.PCPSource
import OAI.Computability.PerfectCompleteness.Machines.BinaryInputReduction
import OAI.Computability.PerfectCompleteness.Machines.NormalizationMachine
import OAI.Computability.UniqueGames.Machines.GraphIterationBoundsLemmas
import OAI.Computability.UniqueGames.PCP.LoopInitializationLemmas

namespace OAI


namespace PerfectCompleteness.PreprocessingMachine

open Turing UniqueGamesTheorem.Foundations
open Complexity PCP Target

noncomputable section

def preprocessing : RoundComputation.PreprocessingCertificate PCPSource.baseTable :=
  PreprocessingRuntime.tablePolynomialTime PCPSource.baseTable

theorem preprocessing_finite_alphabet :
    MachineFiniteAlphabet.FiniteAlphabet preprocessing.tm :=
  PreprocessingRuntime.finiteAlphabet PCPSource.baseTable

def round :
    TM2ComputableInPolyTime GraphTables.tableBits GraphTables.tableBits
      (RoundTables.build PCPSource.baseTable) :=
  RoundComputation.tablePolynomialTime PCPSource.baseTable preprocessing

theorem round_finite_alphabet : MachineFiniteAlphabet.FiniteAlphabet round.tm :=
  RoundComputation.tablePolynomialTime_finite_alphabet PCPSource.baseTable
    preprocessing preprocessing_finite_alphabet

def computableInPolyTime :
    TM2ComputableInPolyTime formulaBits formulaBits PCPSource.rawFormula :=
  MachineTableIteration.gapMapCertificate PCPSource.baseTable round

theorem finite_alphabet :
    MachineFiniteAlphabet.FiniteAlphabet computableInPolyTime.tm :=
  TableIterationFiniteAlphabet.gapMap PCPSource.baseTable round round_finite_alphabet

end
end PerfectCompleteness.PreprocessingMachine


namespace PerfectCompleteness.PCPSourceMachine

open Turing UniqueGamesTheorem.Foundations Complexity Target

noncomputable section

def normalizedComputation :
    TM2ComputableInPolyTime formulaBits formulaBits PCPSource.normalizedFormula := by
  change TM2ComputableInPolyTime formulaBits formulaBits
    (fun formula => Normalization.normalize (PCPSource.rawFormula formula))
  exact MachineSequential.composeBits PreprocessingMachine.computableInPolyTime
    NormalizationMachine.computableInPolyTime

theorem normalized_finiteAlphabet :
    MachineFiniteAlphabet.FiniteAlphabet normalizedComputation.tm :=
  MachineFiniteAlphabet.composeBits PreprocessingMachine.computableInPolyTime
    NormalizationMachine.computableInPolyTime PreprocessingMachine.finite_alphabet
    NormalizationMachine.computation_finiteAlphabet

def rawSource (input : List Bool) : Formula :=
  PCPSource.normalizedFormula (BinaryLanguage.totalRename input)

def rawComputation : TM2ComputableInPolyTime (id : List Bool → List Bool) formulaBits rawSource := by
  change TM2ComputableInPolyTime (id : List Bool → List Bool) formulaBits
    (fun input => PCPSource.normalizedFormula (BinaryLanguage.totalRename input))
  exact MachineSequential.composeBits BinaryInputReduction.computation normalizedComputation

theorem raw_finiteAlphabet : MachineFiniteAlphabet.FiniteAlphabet rawComputation.tm :=
  MachineFiniteAlphabet.composeBits BinaryInputReduction.computation normalizedComputation
    BinaryInputReduction.computation_finiteAlphabet normalized_finiteAlphabet

theorem rawSource_nonempty (input : List Bool) : (rawSource input).clauses ≠ [] :=
  PCPSource.normalizedFormula_nonempty _

theorem rawSource_satisfiable_iff (input : List Bool) :
    (rawSource input).Satisfiable ↔ BinaryLanguage.language input :=
  (PCPSource.normalizedFormula_satisfiable_iff (BinaryLanguage.totalRename input)).trans
    (BinaryLanguage.totalRename_satisfiable_iff input)

theorem rawSource_distinct (input : List Bool) (clause : Clause (rawSource input).variables)
    (mem : clause ∈ (rawSource input).clauses) (i j : Fin 3)
    (same : clause[i].variableIndex = clause[j].variableIndex) : i = j :=
  PCPSource.normalizedFormula_distinct (BinaryLanguage.totalRename input) clause mem i j same

theorem rawSource_clauseGap (input : List Bool) (unsat : ¬BinaryLanguage.language input) :
    SourceAmplification.ClauseGap (PCPSource.clauseFamily (BinaryLanguage.totalRename input))
      PCPSource.sourceGap :=
  PCPSource.clauseGap (BinaryLanguage.totalRename input)
    (fun sat => unsat ((BinaryLanguage.totalRename_satisfiable_iff input).mp sat))

theorem amplifiedSource_complete (input : List Bool) (sat : BinaryLanguage.language input)
    (σ : ℚ) (hσ : 0 < σ) :
    (PCPSource.amplifiedSource (BinaryLanguage.totalRename input) σ hσ).value = 1 :=
  PCPSource.amplifiedSource_complete (BinaryLanguage.totalRename input)
    ((BinaryLanguage.totalRename_satisfiable_iff input).mpr sat) σ hσ

theorem amplifiedSource_sound (input : List Bool) (unsat : ¬BinaryLanguage.language input)
    (σ : ℚ) (hσ : 0 < σ) :
    (PCPSource.amplifiedSource (BinaryLanguage.totalRename input) σ hσ).value < (σ : ℝ) :=
  PCPSource.amplifiedSource_sound (BinaryLanguage.totalRename input)
    (fun sat => unsat ((BinaryLanguage.totalRename_satisfiable_iff input).mp sat)) σ hσ

end
end PerfectCompleteness.PCPSourceMachine

end OAI
