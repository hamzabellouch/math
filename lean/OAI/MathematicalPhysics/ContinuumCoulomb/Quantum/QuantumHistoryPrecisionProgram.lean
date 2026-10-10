import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumHistorySamplerProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPaddedLabelEnergy

namespace OAI

/-! The prescribed sampling precision is computed in unary.  Composition
with the checked local sampler yields the actual early raw exchange compiler. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistoryPrecisionProgram
open ExactQuantumFactoring.BitStackProgram QuantumCircuitCode QuantumAlgebraicHistory

abbrev Input := ℕ × QMACircuit
abbrev inputCode := QuantumHistorySamplerProgram.inputCode

noncomputable opaque coefficientBudgetProgram : Procedure circuitCode unaryCode coefficientBudget := by
  let const (n : ℕ) := Procedure.constant circuitCode unaryCode n
  let inner := Procedure.unaryMul.comp
    ((Procedure.unaryAdd.comp
      ((Procedure.unaryMul.comp ((const 14).pair
        (Procedure.unarySuccessor.comp workProgram))).pair (const 8))).pair
      QuantumHistoryDescriptors.timeProgram)
  exact Procedure.unaryMul.comp ((const 128).pair
    (Procedure.unaryAdd.comp ((const 14).pair
      (Procedure.unaryMul.comp ((const 288).pair inner)))))

noncomputable opaque termBudgetProgram : Procedure circuitCode unaryCode termBudget :=
  (Procedure.unaryMul.comp
    ((Procedure.constant circuitCode unaryCode 4096).pair
      QuantumHistorySamplerProgram.countProgram)).congrFun (by
        intro c
        simp only [termBudget,Function.comp_apply,QuantumOrderedSourceIndex.referenceCount_eq])

noncomputable opaque circuitProgram : Procedure inputCode circuitCode Prod.snd :=
  Procedure.second _ _
noncomputable opaque inverseErrorProgram : Procedure inputCode unaryCode Prod.fst :=
  Procedure.first _ _

noncomputable opaque termAllowanceProgram : Procedure inputCode unaryCode
    (fun x : Input => termBudget x.2+1) :=
  Procedure.unarySuccessor.comp (termBudgetProgram.comp circuitProgram)

noncomputable opaque coefficientAllowanceProgram : Procedure inputCode unaryCode
    (fun x : Input => coefficientBudget x.2+1) :=
  Procedure.unarySuccessor.comp (coefficientBudgetProgram.comp circuitProgram)

noncomputable opaque precisionFactorProgram : Procedure inputCode unaryCode
    (fun x : Input => (termBudget x.2+1)*(coefficientBudget x.2+1)) :=
  Procedure.unaryMul.comp (termAllowanceProgram.pair coefficientAllowanceProgram)

noncomputable opaque precisionProgram : Procedure inputCode unaryCode
    (fun x : Input => samplePrecision x.2 x.1) :=
  (Procedure.unaryMul.comp (precisionFactorProgram.pair inverseErrorProgram)).congrFun
    (by intro x; rfl)

noncomputable opaque sourceQubitsProgram : Procedure circuitCode unaryCode
    QuantumOrderedSourceIndex.qubitCount := by
  let const (n : ℕ) := Procedure.constant circuitCode unaryCode n
  let clocks := Procedure.unaryMul.comp ((const 3).pair QuantumHistoryDescriptors.timeProgram)
  let work := Procedure.unaryMul.comp ((const 2).pair workProgram)
  exact (Procedure.unaryAdd.comp
    ((Procedure.unaryAdd.comp (clocks.pair work)).pair (const 8))).congrFun (by
      intro c
      simpa only [Function.comp_apply] using (QuantumOrderedSourceIndex.qubitCount_eq c).symm)

def prepare (x : Input) : QuantumOrderedLabelFamily.Input :=
  (x.1,QuantumOrderedSourceIndex.qubitCount x.2,
    QuantumHistorySamplerProgram.entries (samplePrecision x.2 x.1,x.2))

noncomputable opaque prepareProgram : Procedure inputCode QuantumOrderedLabelFamily.inputCode prepare :=
  inverseErrorProgram.pair ((sourceQubitsProgram.comp circuitProgram).pair
    (QuantumHistorySamplerProgram.program.comp (precisionProgram.pair circuitProgram)))

def output (x : Input) : List MediatorListProgram.Bond × ℚ :=
  QuantumOrderedLabelCompile.output (prepare x)

noncomputable opaque outputProgram : Procedure inputCode
    (prodCode (listCode MediatorListProgram.bondCode) ratCode) output :=
  QuantumOrderedLabelCompile.outputProgram.comp prepareProgram

def physicalQubits (x : Input) : ℕ := QuantumOrderedLabelCompile.qubitCount (prepare x)

theorem physicalQubits_eq (x : Input) :
    physicalQubits x=4*QuantumOrderedLabelCompile.outputCount (prepare x) := by
  simp only [physicalQubits,QuantumOrderedLabelCompile.qubitCount,
    QuantumOrderedLabelCompile.outputCount,Function.comp_apply]

noncomputable opaque outputCountProgram : Procedure inputCode unaryCode
    (fun x => QuantumOrderedLabelCompile.outputCount (prepare x)) :=
  QuantumOrderedLabelCompile.outputCountProgram.comp prepareProgram

noncomputable opaque physicalQubitsProgram : Procedure inputCode unaryCode physicalQubits :=
  (Procedure.unaryMul.comp ((Procedure.constant inputCode unaryCode 4).pair
    outputCountProgram)).congrFun (fun x => (physicalQubits_eq x).symm)

theorem prepare_actual (N : ℕ) (c : QMACircuit) (hT : 0<c.gates.length) :
    prepare (N,c)=QuantumPaddedLabelProgram.historyInput c hT N := by
  change (N,QuantumOrderedSourceIndex.qubitCount c,
      QuantumHistorySamplerProgram.entries (samplePrecision c N,c))=
    (N,QuantumOrderedSourceIndex.qubitCount c,
      QuantumPaddedLabelProgram.sourceEntries (samplePrecision c N) c hT)
  rw [QuantumHistorySamplerProgram.entries_actual _ c hT]

theorem output_actual (N : ℕ) (c : QMACircuit) (hT : 0<c.gates.length) :
    output (N,c)=QuantumPaddedLabelProgram.historyOutput c hT N :=
  congrArg QuantumOrderedLabelCompile.output (prepare_actual N c hT)

theorem physicalQubits_actual (N : ℕ) (c : QMACircuit) (hT : 0<c.gates.length) :
    physicalQubits (N,c)=QuantumPaddedLabelProgram.historyQubits c hT N :=
  congrArg QuantumOrderedLabelCompile.qubitCount (prepare_actual N c hT)

noncomputable def certificate : Turing.TM2ComputableInPolyTime inputCode
    (prodCode (listCode MediatorListProgram.bondCode) ratCode) output := outputProgram.toTM2

end ContinuumCoulomb.QuantumHistoryPrecisionProgram

end

end OAI
