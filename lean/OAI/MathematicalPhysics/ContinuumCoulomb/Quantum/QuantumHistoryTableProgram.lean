import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPropagationSampler
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumReferenceEdgeTable
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumDiagonalTableProgram

namespace OAI

/-! Total local-table dispatcher for the literal history order.  Its seven
arity templates are fixed; only descriptor and short-label reads vary. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistoryTableProgram
open ExactQuantumFactoring.BitStackProgram QuantumCircuitCode QuantumHistoryDescriptors
open QuantumAlgebraicScalar QuantumFixedPauli
open scoped Classical

abbrev Input := QMACircuit × (ℕ × List ℕ)
def inputCode : Input → List Bool :=
  prodCode circuitCode (prodCode Nat.bits (listCode Nat.bits))

def localTable (n : ℕ) (x : Input) : List Scalar :=
  if x.2.1<referenceWork x.1+1 then
    let a := orderedAt x.1 x.2.1
    if a.1<4 then QuantumHistoryDiagonal.tableList n (x.1,a,x.2.2)
    else QuantumPropagationSampler.tableList n (x.1,a.2,x.2.2.tail)
  else matrixData (QuantumReferenceEdgeTable.table n
    (x.2.1-(referenceWork x.1+1),x.2.2))

noncomputable opaque circuitProgram : Procedure inputCode circuitCode Prod.fst :=
  Procedure.first _ _
noncomputable opaque restProgram : Procedure inputCode
    (prodCode Nat.bits (listCode Nat.bits)) Prod.snd := Procedure.second _ _
noncomputable opaque indexProgram : Procedure inputCode Nat.bits (fun x => x.2.1) :=
  (Procedure.first _ _).comp restProgram
noncomputable opaque labelsProgram : Procedure inputCode (listCode Nat.bits) (fun x => x.2.2) :=
  (Procedure.second _ _).comp restProgram
noncomputable opaque descriptorProgram : Procedure inputCode descriptorCode
    (fun x => orderedAt x.1 x.2.1) :=
  orderedAtProgram.comp (circuitProgram.pair indexProgram)
noncomputable opaque cutoffProgram : Procedure inputCode Nat.bits
    (fun x => referenceWork x.1+1) :=
  Procedure.successor.comp (referenceWorkProgram.comp circuitProgram)

noncomputable opaque localTableProgram (n : ℕ) : Procedure inputCode matrixCode (localTable n) := by
  let diagonal := (QuantumHistoryDiagonal.tableProgram n).comp
    (circuitProgram.pair (descriptorProgram.pair labelsProgram))
  let time := (Procedure.second Nat.bits Nat.bits).comp descriptorProgram
  let propagation := (QuantumPropagationSampler.tableListProgram n).comp
    (circuitProgram.pair (time.pair ((Procedure.listTail Nat.bits).comp labelsProgram)))
  let edge := (QuantumReferenceEdgeTable.tableProgram n).comp
    ((Procedure.binarySub.comp (indexProgram.pair cutoffProgram)).pair labelsProgram)
  let localTest := Procedure.binaryLt.comp (indexProgram.pair cutoffProgram)
  let tag := (Procedure.first Nat.bits Nat.bits).comp descriptorProgram
  let diagonalTest := Procedure.binaryLt.comp
    (tag.pair (Procedure.constant inputCode Nat.bits 4))
  exact (Procedure.conditional localTest
    (Procedure.conditional diagonalTest diagonal propagation) edge).congrFun (by
      intro x
      simp only [localTable,Function.comp_apply,decide_eq_true_eq])

def table (x : Input) : List Scalar :=
  if x.2.2.length=0 then localTable 0 x else
  if x.2.2.length=1 then localTable 1 x else
  if x.2.2.length=2 then localTable 2 x else
  if x.2.2.length=3 then localTable 3 x else
  if x.2.2.length=4 then localTable 4 x else
  if x.2.2.length=5 then localTable 5 x else localTable 6 x

noncomputable opaque tableProgram : Procedure inputCode matrixCode table := by
  let count := Procedure.unaryToBits.comp
    ((ExactQuantumFactoring.NativeAIG.Emission.listUnaryLength Nat.bits 0).comp labelsProgram)
  let test (n : ℕ) := Procedure.binaryEq.comp
    (count.pair (Procedure.constant inputCode Nat.bits n))
  exact (Procedure.conditional (test 0) (localTableProgram 0)
    (Procedure.conditional (test 1) (localTableProgram 1)
    (Procedure.conditional (test 2) (localTableProgram 2)
    (Procedure.conditional (test 3) (localTableProgram 3)
    (Procedure.conditional (test 4) (localTableProgram 4)
    (Procedure.conditional (test 5) (localTableProgram 5) (localTableProgram 6))))))).congrFun
      (by intro x; simp only [table,Function.comp_apply,id_eq,decide_eq_true_eq])

theorem table_eq (x : Input) (h : x.2.2.length≤6) : table x=localTable x.2.2.length x := by
  generalize hn : x.2.2.length=n at *
  interval_cases n <;> simp only [table,hn] <;> norm_num

noncomputable def certificate : Turing.TM2ComputableInPolyTime inputCode matrixCode table :=
  tableProgram.toTM2

end ContinuumCoulomb.QuantumHistoryTableProgram

end

end OAI
