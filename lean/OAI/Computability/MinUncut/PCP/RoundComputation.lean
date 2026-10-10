import Mathlib
import OAI.Computability.MinUncut.PCP.RawInitialTables
import OAI.Computability.MinUncut.Machines.PoweringMachineRuntime

namespace OAI

section
namespace MinUncutGames.Foundations.PCP.RoundComputation

open Turing
open MinUncutGames.Foundations.Complexity


abbrev PreprocessingCertificate (H : RoundTables.BaseTable) :=
  TM2ComputableInPolyTime GraphTables.tableBits
    (PortTables.inputBits (ports := PreprocessingTables.degree))
    (PreprocessingTables.output H)

abbrev PoweringCertificate :=
  TM2ComputableInPolyTime
    (PortTables.inputBits (ports := PreprocessingTables.degree))
    (GenericGraphTables.tableBits (q := RoundTables.alphabet))
    (PoweringTables.transform PreprocessingTables.degree RoundTables.walkParameter)

theorem powered_eq_transform (H : RoundTables.BaseTable) (table : GraphTables.Table) :
    RoundTables.powered H table =
      PoweringTables.transform PreprocessingTables.degree RoundTables.walkParameter
        (PreprocessingTables.output H table) := rfl

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

theorem powered_finiteAlphabet (H : RoundTables.BaseTable)
    (preprocessing : PreprocessingCertificate H) (powering : PoweringCertificate)
    (hpreprocessing : MachineFiniteAlphabet.FiniteAlphabet preprocessing.tm)
    (hpowering : MachineFiniteAlphabet.FiniteAlphabet powering.tm) :
    MachineFiniteAlphabet.FiniteAlphabet
      (poweredPolynomialTimeOfCertificates H preprocessing powering).tm :=
  MachineFiniteAlphabet.composeBits preprocessing powering hpreprocessing hpowering

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

noncomputable def tablePolynomialTime (H : RoundTables.BaseTable)
    (preprocessing : PreprocessingCertificate H) :
    TM2ComputableInPolyTime GraphTables.tableBits GraphTables.tableBits
      (RoundTables.build H) :=
  tablePolynomialTimeOfCertificates H preprocessing
    (PoweringMachineRuntime.computableInPolyTime PreprocessingTables.degree
      RoundTables.walkParameter)

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

end MinUncutGames.Foundations.PCP.RoundComputation

end

end OAI
