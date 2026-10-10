import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkGridProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkListInitialCells

namespace OAI

/-! The initial subdivision computes its row/column array from the actual
endpoint list, before the same fixed-round grid program is applied. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkGridProgram
open QuantumForkList MediatorListProgram ExactQuantumFactoring.BitStackProgram

abbrev InitialCells := ℕ × (List Bond × List QuantumRouteCode.Pair)
def initialCellsCode : InitialCells → List Bool :=
  prodCode unaryCode (prodCode (listCode bondCode) (listCode QuantumRouteCode.pairCode))
def initialQueryCode : (ℕ × InitialCells) → List Bool := prodCode Nat.bits initialCellsCode

noncomputable def initialCellProgram : Procedure initialQueryCode QuantumRouteCode.pairCode
    (fun x => initialCell x.2.1 x.2.2.1 (lookup x.2.2.2) x.1) := by
  let v := Procedure.first Nat.bits initialCellsCode
  let env := Procedure.second Nat.bits initialCellsCode
  let n := Procedure.unaryToBits.comp ((Procedure.first unaryCode
    (prodCode (listCode bondCode) (listCode QuantumRouteCode.pairCode))).comp env)
  let tail := (Procedure.second unaryCode
    (prodCode (listCode bondCode) (listCode QuantumRouteCode.pairCode))).comp env
  let bs := (Procedure.first (listCode bondCode) (listCode QuantumRouteCode.pairCode)).comp tail
  let cells := (Procedure.second (listCode bondCode) (listCode QuantumRouteCode.pairCode)).comp tail
  let endpoint := initialEndpointProgram.comp ((Procedure.binarySub.comp (v.pair n)).pair bs)
  let target := Procedure.conditional (Procedure.binaryLt.comp (v.pair n)) v endpoint
  exact ((Procedure.listGet QuantumRouteCode.pairCode (0,0)).comp (target.pair cells)).congrFun (by
    intro x
    change lookup x.2.2.2 (if decide (x.1<x.2.1) then x.1 else
      initialEndpoint x.2.2.1 (x.1-x.2.1)) = _
    unfold initialCell
    by_cases h : x.1<x.2.1 <;> simp [h])

def initialCells (x : InitialCells) : List QuantumRouteCode.Pair :=
  (List.range (x.1+2*x.2.1.length)).map (initialCell x.1 x.2.1 (lookup x.2.2))

noncomputable def initialCellsProgram :
    Procedure initialCellsCode (listCode QuantumRouteCode.pairCode) initialCells := by
  let n := Procedure.first unaryCode
    (prodCode (listCode bondCode) (listCode QuantumRouteCode.pairCode))
  let bs := (Procedure.first (listCode bondCode) (listCode QuantumRouteCode.pairCode)).comp
    (Procedure.second unaryCode (prodCode (listCode bondCode) (listCode QuantumRouteCode.pairCode)))
  let len := (ExactQuantumFactoring.NativeAIG.Emission.listUnaryLength bondCode (0,0,0)).comp bs
  let count := Procedure.unaryAdd.comp (n.pair (Procedure.unaryAdd.comp (len.pair len)))
  let query : Procedure (prodCode unaryCode initialCellsCode) initialQueryCode
      (fun x => (x.1,x.2)) :=
    (Procedure.unaryToBits.comp (Procedure.first unaryCode initialCellsCode)).pair
      (Procedure.second unaryCode initialCellsCode)
  exact ((Procedure.tabulate (f := fun x i => initialCell x.1 x.2.1 (lookup x.2.2) i)
    (0,0) (initialCellProgram.comp query)).comp
      (count.pair (Procedure.identity initialCellsCode))).congrFun (by
        intro x
        change (List.range (x.1+(x.2.1.length+x.2.1.length))).map _=initialCells x
        simp only [initialCells,two_mul,id_eq])

theorem lookup_initialCells (x : InitialCells) (v : ℕ) (hv : v<x.1+2*x.2.1.length) :
    lookup (initialCells x) v=initialCell x.1 x.2.1 (lookup x.2.2) v := by
  simp only [lookup,initialCells,List.headD_eq_head?_getD,List.head?_drop]
  rw [List.getElem?_eq_getElem (by simpa only [List.length_map,List.length_range] using hv)]
  simp only [Option.getD_some,List.getElem_map,List.getElem_range]

abbrev PreparedInput := InitialInput × List QuantumRouteCode.Pair
def preparedCode : PreparedInput → List Bool :=
  prodCode initialInputCode (listCode QuantumRouteCode.pairCode)

def prepare (x : PreparedInput) : Input :=
  (x.1.1,(initial x.1.2.1 x.1.2.2.1 x.1.2.2.2 x.1.1,
    initialCells (x.1.2.1,x.1.2.2.1,x.2)))

noncomputable def prepareProgram : Procedure preparedCode inputCode prepare := by
  let init := Procedure.first initialInputCode (listCode QuantumRouteCode.pairCode)
  let cells := Procedure.second initialInputCode (listCode QuantumRouteCode.pairCode)
  let n := initialInputCount.comp init
  let bs := initialInputBonds.comp init
  let r := (Procedure.first ratCode
    (prodCode unaryCode (prodCode (listCode bondCode) ratCode))).comp init
  exact r.pair ((initialStateProgram.comp init).pair
    (initialCellsProgram.comp (n.pair (bs.pair cells))))

def output (k : ℕ) (x : PreparedInput) : Cells := run k (prepare x)

noncomputable def outputProgram (k : ℕ) : Procedure preparedCode cellsCode (output k) :=
  (runProgram k).comp prepareProgram

theorem output_state (k : ℕ) (x : PreparedInput) :
    (output k x).1=iterate x.1.1 k
      (initial x.1.2.1 x.1.2.2.1 x.1.2.2.2 x.1.1) := run_state k (prepare x)

theorem output_length (k : ℕ) (x : PreparedInput) :
    (output k x).2.length=(output k x).1.1 := by
  apply run_length
  simp only [prepare,initialCells,List.length_map,List.length_range,initial]

theorem prepare_represents (x : PreparedInput) :
    Represents (prepare x).2 (initialCell x.1.2.1 x.1.2.2.1 (lookup x.2)) := by
  intro v hv
  exact lookup_initialCells _ v hv

theorem output_represents (k : ℕ) (x : PreparedInput) :
    Represents (output k x)
      (iterateCell x.1.1 k (initial x.1.2.1 x.1.2.2.1 x.1.2.2.2 x.1.1)
        (initialCell x.1.2.1 x.1.2.2.1 (lookup x.2))) :=
  run_represents k (prepare x) (initial_validPorts _ _ _ _) _ (prepare_represents x)

end ContinuumCoulomb.QuantumForkGridProgram

end

end OAI
