import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumLaneUnaryProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPortRankActual
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumBufferedListProgram

namespace OAI

/-! Compile cell arrays and an edge array into the registers needed by the
buffered-route evaluator. Binary endpoint labels are clipped by the explicit
qubit array length before their conversion to unary loop bounds. -/

noncomputable section
namespace ContinuumCoulomb.QuantumRoutingInputProgram
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode

abbrev Data := (List Pair × List Pair) × List Pair
def dataCode : Data → List Bool :=
  prodCode (prodCode (listCode pairCode) (listCode pairCode)) (listCode pairCode)
abbrev Input := ℕ × Data
def inputCode : Input → List Bool := prodCode unaryCode dataCode

def edge (d : Data) (i : ℕ) : Pair := QuantumPathVisitProgram.lookup d.2 i
def lane (B : ℕ) (x : Input) : ℕ := QuantumSpatialSlotProgram.lane B (x.1,x.2.1.2)
def entry (B : ℕ) (d : Data) (i : ℕ) : QuantumPortRankProgram.Entry :=
  ((edge d i).1,(edge d i).2,lane B (i,d))
def entries (B : ℕ) (d : Data) : List QuantumPortRankProgram.Entry :=
  (List.range d.2.length).map (entry B d)

def fine (A : ℕ) (d : Data) (a : ℕ) : Pair :=
  QuantumSpatialSlotProgram.fineSite A (min d.1.1.length a,d.1.1)

def value (A B : ℕ) (x : Input) : QuantumBufferedListProgram.Input :=
  let e := edge x.2 x.1
  let c := lane B x
  let es := entries B x.2
  ((fine A x.2 e.1,fine A x.2 e.2),c,
    QuantumPortRankProgram.value ((e.1,c),es),
    QuantumPortRankProgram.value ((e.2,c),es))

noncomputable def dataProgram : Procedure inputCode dataCode Prod.snd := Procedure.second _ _
noncomputable def indexProgram : Procedure inputCode unaryCode Prod.fst := Procedure.first _ _
noncomputable def qubitsProgram : Procedure inputCode (listCode pairCode) (fun x => x.2.1.1) :=
  (Procedure.first (listCode pairCode) (listCode pairCode)).comp
    ((Procedure.first (prodCode (listCode pairCode) (listCode pairCode)) (listCode pairCode)).comp dataProgram)
noncomputable def anchorsProgram : Procedure inputCode (listCode pairCode) (fun x => x.2.1.2) :=
  (Procedure.second (listCode pairCode) (listCode pairCode)).comp
    ((Procedure.first (prodCode (listCode pairCode) (listCode pairCode)) (listCode pairCode)).comp dataProgram)
noncomputable def edgesProgram : Procedure inputCode (listCode pairCode) (fun x => x.2.2) :=
  (Procedure.second (prodCode (listCode pairCode) (listCode pairCode)) (listCode pairCode)).comp dataProgram

noncomputable def edgeProgram : Procedure inputCode pairCode (fun x => edge x.2 x.1) :=
  (Procedure.listGet pairCode (0,0)).comp
    ((Procedure.unaryToBits.comp indexProgram).pair edgesProgram)

noncomputable def laneProgram (B : ℕ) : Procedure inputCode Nat.bits (lane B) :=
  (QuantumSpatialSlotProgram.laneProgram B).comp (indexProgram.pair anchorsProgram)
noncomputable def laneUnaryProgram (B : ℕ) : Procedure inputCode unaryCode (lane B) :=
  (QuantumLaneUnaryProgram.program B).comp (indexProgram.pair anchorsProgram)

noncomputable def entryProgram (B : ℕ) : Procedure inputCode QuantumPortRankProgram.entryCode
    (fun x => entry B x.2 x.1) :=
  ((Procedure.first Nat.bits Nat.bits).comp edgeProgram).pair
    (((Procedure.second Nat.bits Nat.bits).comp edgeProgram).pair (laneProgram B))

noncomputable def entriesProgram (B : ℕ) :
    Procedure dataCode (listCode QuantumPortRankProgram.entryCode) (entries B) := by
  let edges := Procedure.second (prodCode (listCode pairCode) (listCode pairCode)) (listCode pairCode)
  let n := (ExactQuantumFactoring.NativeAIG.Emission.listUnaryLength pairCode (0,0)).comp edges
  exact (Procedure.tabulate (f := entry B) (0,0,0) (entryProgram B)).comp
    (n.pair (Procedure.identity dataCode))

noncomputable def program (A B : ℕ) :
    Procedure inputCode QuantumBufferedListProgram.inputCode (value A B) := by
  let left := (Procedure.first Nat.bits Nat.bits).comp edgeProgram
  let right := (Procedure.second Nat.bits Nat.bits).comp edgeProgram
  let n := (ExactQuantumFactoring.NativeAIG.Emission.listUnaryLength pairCode (0,0)).comp qubitsProgram
  let leftIndex := Procedure.clippedUnary.comp (n.pair left)
  let rightIndex := Procedure.clippedUnary.comp (n.pair right)
  let leftPoint := (QuantumSpatialSlotProgram.fineSiteProgram A).comp (leftIndex.pair qubitsProgram)
  let rightPoint := (QuantumSpatialSlotProgram.fineSiteProgram A).comp (rightIndex.pair qubitsProgram)
  let es := (entriesProgram B).comp dataProgram
  let leftPort := QuantumPortRankProgram.program.comp ((left.pair (laneProgram B)).pair es)
  let rightPort := QuantumPortRankProgram.program.comp ((right.pair (laneProgram B)).pair es)
  exact (leftPoint.pair rightPoint).pair ((laneUnaryProgram B).pair (leftPort.pair rightPort))

noncomputable def pathProgram (A B : ℕ) : Procedure inputCode (listCode pairCode)
    (fun x => QuantumBufferedListProgram.path A B (value A B x)) :=
  (QuantumBufferedListProgram.pathProgram A B).comp (program A B)

end ContinuumCoulomb.QuantumRoutingInputProgram

end

end OAI
