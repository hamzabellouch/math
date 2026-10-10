import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPaddedLabelTable
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumOrderedLabelCompile

namespace OAI

/-! Polynomial postprocessing of the actual fixed-size local matrix
payloads.  This emits the full raw exchange list and its scalar offset. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPaddedPacketProgram
open ExactQuantumFactoring.BitStackProgram QuantumFixedPauli

abbrev Payload := List ℕ × List QuantumAlgebraicScalar.Scalar
def payloadCode : Payload → List Bool := prodCode (listCode Nat.bits) matrixCode
abbrev FamilyInput := ℕ × List Payload
def familyCode : FamilyInput → List Bool := prodCode unaryCode (listCode payloadCode)

def family (x : FamilyInput) : List QuantumOrderedLabelFamily.Entry :=
  (x.2.map (fun p => QuantumPaddedLabelProgram.uniformPacket (x.1,p))).flatten

noncomputable opaque familyProgram : Procedure familyCode
    (listCode QuantumOrderedLabelFamily.entryCode) family :=
  (QuantumRawExchange.flattenProgram QuantumOrderedLabelFamily.entryCode ([],0)).comp
    (Procedure.listMapWith (ea := unaryCode) (eb := payloadCode)
      (ec := listCode QuantumOrderedLabelFamily.entryCode)
      (f := fun k p => QuantumPaddedLabelProgram.uniformPacket (k,p))
      ([],[]) [] QuantumPaddedLabelProgram.uniformProgram)

abbrev Input := ℕ × (ℕ × FamilyInput)
def inputCode : Input → List Bool :=
  prodCode unaryCode (prodCode unaryCode familyCode)

def prepare (x : Input) : QuantumOrderedLabelFamily.Input :=
  (x.1,x.2.1,family x.2.2)

noncomputable opaque prepareProgram : Procedure inputCode
    QuantumOrderedLabelFamily.inputCode prepare :=
  (Procedure.first unaryCode (prodCode unaryCode familyCode)).pair
    (((Procedure.first unaryCode familyCode).comp
      (Procedure.second unaryCode (prodCode unaryCode familyCode))).pair
      (familyProgram.comp ((Procedure.second unaryCode familyCode).comp
        (Procedure.second unaryCode (prodCode unaryCode familyCode)))))

def output (x : Input) := QuantumOrderedLabelCompile.output (prepare x)

noncomputable opaque outputProgram : Procedure inputCode
    (prodCode (listCode MediatorListProgram.bondCode) ratCode) output :=
  QuantumOrderedLabelCompile.outputProgram.comp prepareProgram

noncomputable def certificate : Turing.TM2ComputableInPolyTime inputCode
    (prodCode (listCode MediatorListProgram.bondCode) ratCode) output := outputProgram.toTM2

open QuantumPaddedLabelProgram QuantumOrderedSourceIndex
open scoped Classical

local instance finDecision (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

def sourcePayloads (c : QMACircuit) (hT : 0 < c.gates.length) : List Payload :=
  List.ofFn (fun i : Fin (referenceCount c) =>
    (QuantumOrderedSupport.encodedSites c hT (reference c i),
      matrixData (QuantumAlgebraicHistory.orderedTable c hT (reference c i))))

theorem family_source (k : ℕ) (c : QMACircuit) (hT : 0 < c.gates.length) :
    family (k,sourcePayloads c hT)=sourceEntries k c hT := by
  simp only [family,sourcePayloads,sourceEntries,sourceInput,List.map_ofFn,
    Function.comp_def]

end ContinuumCoulomb.QuantumPaddedPacketProgram

end

end OAI
