import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumTaggedRouteProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumParallelRouteSearch

namespace OAI

/-! A literal 140-entry selector checks finite permissions and both physical
endpoints. No unbounded search or choice occurs in the resulting program. -/

noncomputable section
namespace ContinuumCoulomb.QuantumRouteSelectorProgram
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode
open QuantumTaggedRouteProgram QuantumFiniteRouteSearch

abbrev Ends := Pair × Pair
def endsCode : Ends → List Bool := prodCode pairCode pairCode
def accepts (ends : Ends) (v : Tagged) : Bool :=
  v.1 && decide (v.2.headD (0,0) = ends.1) && decide (v.2.reverse.headD (0,0) = ends.2)

noncomputable opaque matchProgram : Procedure (prodCode endsCode taggedCode) Procedure.boolCode
    (fun x => accepts x.1 x.2) := by
  let ends := Procedure.first endsCode taggedCode
  let tag := Procedure.second endsCode taggedCode
  let bit := (Procedure.first Procedure.boolCode (listCode pairCode)).comp tag
  let path := (Procedure.second Procedure.boolCode (listCode pairCode)).comp tag
  let head := (Procedure.listHead pairCode (0,0)).comp path
  let last := (Procedure.listHead pairCode (0,0)).comp
    ((Procedure.listReverse pairCode (0,0)).comp path)
  let left := QuantumFiniteMembership.pairEqProgram.comp
    (head.pair ((Procedure.first pairCode pairCode).comp ends))
  let right := QuantumFiniteMembership.pairEqProgram.comp
    (last.pair ((Procedure.second pairCode pairCode).comp ends))
  exact Procedure.boolAnd.comp ((Procedure.boolAnd.comp (bit.pair left)).pair right)

def choose (x : Ends × List Tagged) : List Pair :=
  (selectParallelValue (false,[]) (x.2,x.2.map (accepts x.1))).2

noncomputable opaque chooseProgram : Procedure (prodCode endsCode (listCode taggedCode))
    (listCode pairCode) choose := by
  let bits := Procedure.listMapWith (false,[]) false matchProgram
  let tags := Procedure.second endsCode (listCode taggedCode)
  let chosen := (selectParallelProgram taggedCode (false,[])).comp (tags.pair bits)
  exact (Procedure.second Procedure.boolCode (listCode pairCode)).comp chosen

abbrev Input := QuantumRoutingTable.Table × Ends
def inputCode : Input → List Bool := prodCode QuantumRoutingTable.tableCode endsCode

def candidates (x : Input) : List Tagged :=
  (qmaRouteCandidates x.2.1 x.2.2).map (tagged x.1)

noncomputable opaque candidatesProgram : Procedure inputCode (listCode taggedCode) candidates := by
  let table := Procedure.first QuantumRoutingTable.tableCode endsCode
  let ends := Procedure.second QuantumRoutingTable.tableCode endsCode
  let leftCell := QuantumCellPathProgram.pointCellProgram.comp
    ((Procedure.first pairCode pairCode).comp ends)
  let rightCell := QuantumCellPathProgram.pointCellProgram.comp
    ((Procedure.second pairCode pairCode).comp ends)
  let left := QuantumTaggedRouteProgram.cellProgram.comp (table.pair leftCell)
  let right := QuantumTaggedRouteProgram.cellProgram.comp (table.pair rightCell)
  exact ((Procedure.listAppend taggedCode (false,[])).comp (left.pair right)).congrFun (by
    intro x
    simp only [Function.comp_apply,candidates,qmaRouteCandidates,List.map_append])

def value (x : Input) : List Pair := choose (x.2,candidates x)

noncomputable opaque program : Procedure inputCode (listCode pairCode) value :=
  chooseProgram.comp ((Procedure.second _ _).pair candidatesProgram)

noncomputable def certificate : Turing.TM2ComputableInPolyTime inputCode (listCode pairCode) value :=
  program.toTM2

end ContinuumCoulomb.QuantumRouteSelectorProgram

end

end OAI
