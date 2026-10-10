import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkListData
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRawFamilyProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRoutingProgram

namespace OAI

/-! Literal finite-list programs for the active-port pairs in a fork round.
Only the finite input lists are enumerated; spin Hilbert-space bases are absent. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open ExactQuantumFactoring.BitStackProgram

def portCode : Port → List Bool := prodCode Nat.bits ratCode
def pairCode : Pair → List Bool := prodCode portCode portCode
def groupsCode : Groups → List Bool := listCode (listCode portCode)
def taggedCode : TaggedPair → List Bool := prodCode Nat.bits pairCode
def stateCode : State → List Bool :=
  prodCode unaryCode (prodCode (listCode MediatorListProgram.bondCode)
    (prodCode ratCode groupsCode))

noncomputable def halfProgram : Procedure unaryCode unaryCode (fun n => n/2) := by
  let n := Procedure.identity unaryCode
  let half := Procedure.binaryDiv.comp
    (Procedure.unaryToBits.pair (Procedure.constant unaryCode Nat.bits 2))
  exact (Procedure.clippedUnary.comp (n.pair half)).congrFun (by
    intro n
    exact Nat.min_eq_right (Nat.div_le_self n 2))

noncomputable def portAtProgram :
    Procedure (prodCode unaryCode (listCode portCode)) portCode
      (fun x => portAt x.2 x.1) :=
  (Procedure.listGet portCode (0,0)).comp
    ((Procedure.unaryToBits.comp (Procedure.first unaryCode (listCode portCode))).pair
      (Procedure.second unaryCode (listCode portCode)))

noncomputable def pairAtProgram :
    Procedure (prodCode unaryCode (listCode portCode)) pairCode
      (fun x => (portAt x.2 (2*x.1),portAt x.2 (2*x.1+1))) := by
  let i := Procedure.first unaryCode (listCode portCode)
  let xs := Procedure.second unaryCode (listCode portCode)
  let twice := (Procedure.unaryAdd.comp (i.pair i)).congrFun (by intro x; change x.1+x.1=2*x.1; omega)
  exact (portAtProgram.comp (twice.pair xs)).pair
    (portAtProgram.comp ((Procedure.unarySuccessor.comp twice).pair xs))

noncomputable def pairsProgram : Procedure (listCode portCode) (listCode pairCode) pairs := by
  let count := halfProgram.comp (ExactQuantumFactoring.NativeAIG.Emission.listUnaryLength portCode (0,0))
  exact (Procedure.tabulate (f := fun ps i => (portAt ps (2*i),portAt ps (2*i+1)))
    ((0,0),(0,0)) pairAtProgram).comp (count.pair (Procedure.identity (listCode portCode)))

noncomputable def unpairedProgram : Procedure (listCode portCode) (listCode portCode) unpaired := by
  let count := halfProgram.comp (ExactQuantumFactoring.NativeAIG.Emission.listUnaryLength portCode (0,0))
  let cut := Procedure.unaryToBits.comp (Procedure.unaryAdd.comp (count.pair count))
  exact ((Procedure.listDrop portCode).comp (cut.pair (Procedure.identity (listCode portCode)))).congrFun
    (by intro ps; change ps.drop (ps.length/2+ps.length/2)=ps.drop (2*(ps.length/2)); rw [two_mul])

noncomputable def groupAtProgram : Procedure (prodCode unaryCode groupsCode) (listCode portCode)
    (fun x => groupAt x.2 x.1) :=
  (Procedure.listGet (listCode portCode) []).comp
    ((Procedure.unaryToBits.comp (Procedure.first unaryCode groupsCode)).pair
      (Procedure.second unaryCode groupsCode))

noncomputable def taggedPairsProgram :
    Procedure (prodCode unaryCode groupsCode) (listCode taggedCode)
      (fun x => (pairs (groupAt x.2 x.1)).map (fun p => (x.1,p))) := by
  let i := Procedure.first unaryCode groupsCode
  let ps := pairsProgram.comp groupAtProgram
  let step : Procedure (prodCode Nat.bits pairCode) taggedCode (fun x : ℕ × Pair => (x.1,x.2)) :=
    Procedure.identity taggedCode
  exact (Procedure.listMapWith (f := fun (i : ℕ) (p : Pair) => (i,p))
    ((0,0),(0,0)) (0,((0,0),(0,0))) step).comp
    ((Procedure.unaryToBits.comp i).pair ps)

noncomputable def catalogProgram : Procedure groupsCode (listCode taggedCode) catalog := by
  let count := ExactQuantumFactoring.NativeAIG.Emission.listUnaryLength (listCode portCode) []
  let blocks := (Procedure.tabulate (f := fun gs i =>
    (pairs (groupAt gs i)).map (fun p => (i,p))) [] taggedPairsProgram).comp
      (count.pair (Procedure.identity groupsCode))
  exact (QuantumRawExchange.flattenProgram taggedCode (0,((0,0),(0,0)))).comp blocks

noncomputable def pairCountProgram : Procedure groupsCode unaryCode pairCount :=
  ((ExactQuantumFactoring.NativeAIG.Emission.listUnaryLength taggedCode (0,((0,0),(0,0)))).comp
    catalogProgram).congrFun catalog_length

noncomputable def retainedProgram : Procedure stateCode (listCode ratCode) retained := by
  let tail := Procedure.second unaryCode
    (prodCode (listCode MediatorListProgram.bondCode) (prodCode ratCode groupsCode))
  let bs := (Procedure.first (listCode MediatorListProgram.bondCode) (prodCode ratCode groupsCode)).comp tail
  let gs := (Procedure.second ratCode groupsCode).comp
    ((Procedure.second (listCode MediatorListProgram.bondCode) (prodCode ratCode groupsCode)).comp tail)
  let weights := (Procedure.listMap (0,0,0) 0
    ((Procedure.second Nat.bits ratCode).comp
      (Procedure.second Nat.bits (prodCode Nat.bits ratCode)))).comp bs
  let leftovers := (QuantumRawExchange.flattenProgram portCode (0,0)).comp
    ((Procedure.listMap [] [] unpairedProgram).comp gs)
  let leftoverWeights := (Procedure.listMap (0,0) 0 (Procedure.second Nat.bits ratCode)).comp leftovers
  exact (Procedure.listAppend ratCode 0).comp (weights.pair leftoverWeights)

end ContinuumCoulomb.QuantumForkList

end

end OAI
