import OAI.Computability.PerfectCompleteness.Machines.BinaryRenameMachine
import OAI.Computability.PerfectCompleteness.Machines.BinaryTotalInputMachine
import OAI.Computability.UniqueGames.Machines.MachineLemmas

namespace OAI

section

namespace PerfectCompleteness.BinaryInputReduction

open Turing UniqueGamesTheorem.Foundations.Complexity

noncomputable def computation :
    TM2ComputableInPolyTime (id : List Bool → List Bool) formulaBits BinaryLanguage.totalRename := by
  change TM2ComputableInPolyTime (id : List Bool → List Bool) formulaBits
    (fun input => BinaryOccurrenceRename.renamed (BinaryLanguage.totalParsed input))
  exact MachineSequential.composeBits BinaryTotalInputMachine.computableInPolyTime
    BinaryRenameMachine.computableInPolyTime

theorem computation_finiteAlphabet : MachineFiniteAlphabet.FiniteAlphabet computation.tm :=
  MachineFiniteAlphabet.composeBits BinaryTotalInputMachine.computableInPolyTime
    BinaryRenameMachine.computableInPolyTime
    BinaryTotalInputMachine.computation_finiteAlphabet
    BinaryRenameMachine.computation_finiteAlphabet

noncomputable def reduction : CookLevin.PolynomialThreeSATReduction BinaryLanguage.language where
  reduce := BinaryLanguage.totalRename
  computation := computation
  correct input := (BinaryLanguage.totalRename_satisfiable_iff input).symm

theorem reduction_finiteAlphabet : MachineFiniteAlphabet.FiniteAlphabet reduction.computation.tm :=
  computation_finiteAlphabet

end PerfectCompleteness.BinaryInputReduction

end

end OAI
