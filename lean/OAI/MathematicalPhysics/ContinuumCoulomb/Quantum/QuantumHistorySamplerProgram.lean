import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumHistoryTableCorrectness
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPaddedLabelTable

namespace OAI

/-! Literal polynomial generation of all sampled history packets.  The
runtime list is indexed by the unary number of source terms, not Hilbert-space
dimension; each local matrix uses one of seven fixed arity programs. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistorySamplerProgram
open ExactQuantumFactoring.BitStackProgram QuantumCircuitCode QuantumHistoryDescriptors
open QuantumAlgebraicScalar QuantumFixedPauli
open scoped Classical

local instance finDecision (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

private theorem matrixData_instances {β : Type} (F G : Fintype β)
    (A : Matrix β β Scalar) : @matrixData β F A=@matrixData β G A := by
  cases Subsingleton.elim F G
  rfl

private theorem pair_matrixData_instances {β : Type} (F G : Fintype β)
    (A : Matrix β β Scalar) (xs : List ℕ) :
    (xs,@matrixData β F A)=(xs,@matrixData β G A) :=
  congrArg (fun ys : List Scalar => (xs,ys)) (matrixData_instances F G A)

abbrev Input := ℕ × QMACircuit
def inputCode : Input → List Bool := prodCode unaryCode circuitCode

def packet (x : Input) (i : ℕ) : List QuantumOrderedLabelFamily.Entry :=
  let labels := supportLabels x.2 i
  QuantumPaddedLabelProgram.uniformPacket
    (x.1,labels,QuantumHistoryTableProgram.table (x.2,i,labels))

def entries (x : Input) : List QuantumOrderedLabelFamily.Entry :=
  (List.ofFn (fun i : Fin (QuantumOrderedSourceIndex.referenceCount x.2) => packet x i.val)).flatten

noncomputable opaque countProgram : Procedure circuitCode unaryCode
    QuantumOrderedSourceIndex.referenceCount := by
  let t := Procedure.unaryMul.comp
    ((Procedure.constant circuitCode unaryCode 4).pair timeProgram)
  let w := Procedure.unaryMul.comp
    ((Procedure.constant circuitCode unaryCode 2).pair workProgram)
  exact (Procedure.unaryAdd.comp
    ((Procedure.unaryAdd.comp (t.pair w)).pair
      (Procedure.constant circuitCode unaryCode 9))).congrFun (by
        intro c
        simpa only [Function.comp_apply] using (QuantumOrderedSourceIndex.referenceCount_eq c).symm)

noncomputable opaque packetProgram : Procedure (prodCode unaryCode inputCode)
    (listCode QuantumOrderedLabelFamily.entryCode) (fun x => packet x.2 x.1) := by
  let i := Procedure.unaryToBits.comp (Procedure.first unaryCode inputCode)
  let x := Procedure.second unaryCode inputCode
  let k := (Procedure.first unaryCode circuitCode).comp x
  let c := (Procedure.second unaryCode circuitCode).comp x
  let labels := supportLabelsProgram.comp (c.pair i)
  let matrix := QuantumHistoryTableProgram.tableProgram.comp (c.pair (i.pair labels))
  exact QuantumPaddedLabelProgram.uniformProgram.comp (k.pair (labels.pair matrix))

noncomputable opaque program : Procedure inputCode
    (listCode QuantumOrderedLabelFamily.entryCode) entries := by
  let c := Procedure.second unaryCode circuitCode
  let nested := (Procedure.tabulate (f := fun x i => packet x i) [] packetProgram).comp
    ((countProgram.comp c).pair (Procedure.identity inputCode))
  exact ((QuantumRawExchange.flattenProgram QuantumOrderedLabelFamily.entryCode ([],0)).comp
    nested).congrFun (by
      intro x
      simp only [Function.comp_apply,id_eq,entries]
      apply congrArg List.flatten
      simpa only [List.length_range,List.getElem_range,Fin.val_cast] using
        (List.ofFn_getElem_eq_map (List.range (QuantumOrderedSourceIndex.referenceCount x.2))
          (packet x)).symm)

theorem packet_actual (k : ℕ) (c : QMACircuit) (hT : 0<c.gates.length)
    (i : Fin (QuantumOrderedSourceIndex.referenceCount c)) :
    packet (k,c) i.val=QuantumPaddedLabelProgram.uniformPacket
      (QuantumPaddedLabelProgram.sourceInput k c hT (QuantumOrderedSourceIndex.reference c i)) := by
  let a := QuantumOrderedSourceIndex.reference c i
  have hi : ((QuantumOrderedSourceIndex.reference c).symm a).val=i.val :=
    congrArg Fin.val ((QuantumOrderedSourceIndex.reference c).symm_apply_apply i)
  have hl := supportLabels_actual c hT a
  rw [hi] at hl
  have hm := QuantumHistoryTableProgram.table_actual c hT a
  rw [hi] at hm
  have hp : (supportLabels c i.val,
      QuantumHistoryTableProgram.table (c,i.val,supportLabels c i.val))=
      (QuantumOrderedSupport.encodedSites c hT a,
        matrixData (QuantumAlgebraicHistory.orderedTable c hT a)) := by
    rw [hl,hm]
    exact pair_matrixData_instances
      (β := Fin (QuantumOrderedSupport.sites c hT a).length → Fin 2) _ _
      (QuantumAlgebraicHistory.orderedTable c hT a) (QuantumOrderedSupport.encodedSites c hT a)
  change QuantumPaddedLabelProgram.uniformPacket (k,
      (supportLabels c i.val,QuantumHistoryTableProgram.table (c,i.val,supportLabels c i.val)))=
    QuantumPaddedLabelProgram.uniformPacket (k,
      (QuantumOrderedSupport.encodedSites c hT a,
        matrixData (QuantumAlgebraicHistory.orderedTable c hT a)))
  exact congrArg (fun p => QuantumPaddedLabelProgram.uniformPacket (k,p)) hp

theorem entries_actual (k : ℕ) (c : QMACircuit) (hT : 0<c.gates.length) :
    entries (k,c)=QuantumPaddedLabelProgram.sourceEntries k c hT := by
  unfold entries QuantumPaddedLabelProgram.sourceEntries
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  exact packet_actual k c hT i

noncomputable def certificate : Turing.TM2ComputableInPolyTime inputCode
    (listCode QuantumOrderedLabelFamily.entryCode) entries := program.toTM2

end ContinuumCoulomb.QuantumHistorySamplerProgram

end

end OAI
