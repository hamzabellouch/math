import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumSpatialCrossingProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumListMergeProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRouteSelectorCorrectness

namespace OAI

/-! Merge the physical crossing bonds and compute the short planar route
for every remaining pair of endpoints from the finite permission table. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPlanarTapeProgram
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode MediatorListProgram

abbrev Input := QuantumSpatialCrossingProgram.Output
def inputCode : Input → List Bool := QuantumSpatialCrossingProgram.outputCode
abbrev Output := QuantumListPathStep.Output × (List Pair × List (List Pair))
def outputCode : Output → List Bool := prodCode QuantumListPathStep.outputCode
  (prodCode (listCode pairCode) (listCode (listCode pairCode)))

def merged (x : Input) : List Bond := QuantumListMerge.value x.1.1.1 x.1.1.2.1
def routeInput (x : Input) (e : Bond) : QuantumRouteSelectorProgram.Input :=
  (x.2,QuantumForkGridProgram.lookup x.1.2 e.1,QuantumForkGridProgram.lookup x.1.2 e.2.1)
def paths (x : Input) : List (List Pair) :=
  (merged x).map (fun e => QuantumRouteSelectorProgram.value (routeInput x e))
def value (x : Input) : Output := ((x.1.1.1,merged x,x.1.1.2.2),x.1.2,paths x)

noncomputable opaque packetProgram : Procedure inputCode QuantumListPathStep.outputCode
    (fun x => x.1.1) :=
  (Procedure.first QuantumListPathStep.outputCode (listCode pairCode)).comp
    (Procedure.first (prodCode QuantumListPathStep.outputCode (listCode pairCode))
      QuantumRoutingTable.tableCode)
noncomputable opaque positionsProgram : Procedure inputCode (listCode pairCode)
    (fun x => x.1.2) :=
  (Procedure.second QuantumListPathStep.outputCode (listCode pairCode)).comp
    (Procedure.first (prodCode QuantumListPathStep.outputCode (listCode pairCode))
      QuantumRoutingTable.tableCode)
noncomputable opaque tableProgram : Procedure inputCode QuantumRoutingTable.tableCode
    Prod.snd := Procedure.second _ _
noncomputable opaque nProgram : Procedure inputCode unaryCode (fun x => x.1.1.1) :=
  (Procedure.first unaryCode (prodCode (listCode bondCode) ratCode)).comp packetProgram
noncomputable opaque bondsProgram : Procedure inputCode (listCode bondCode)
    (fun x => x.1.1.2.1) :=
  ((Procedure.first (listCode bondCode) ratCode).comp
    (Procedure.second unaryCode (prodCode (listCode bondCode) ratCode))).comp packetProgram
noncomputable opaque constantProgram : Procedure inputCode ratCode (fun x => x.1.1.2.2) :=
  ((Procedure.second (listCode bondCode) ratCode).comp
    (Procedure.second unaryCode (prodCode (listCode bondCode) ratCode))).comp packetProgram
noncomputable opaque mergedProgram : Procedure inputCode (listCode bondCode) merged :=
  QuantumListMerge.valueProgram.comp (nProgram.pair bondsProgram)

noncomputable opaque routeInputProgram :
    Procedure (prodCode inputCode bondCode) QuantumRouteSelectorProgram.inputCode
      (fun x => routeInput x.1 x.2) := by
  let env := Procedure.first inputCode bondCode
  let e := Procedure.second inputCode bondCode
  let ps := positionsProgram.comp env
  let a := (Procedure.first Nat.bits (prodCode Nat.bits ratCode)).comp e
  let b := ((Procedure.first Nat.bits ratCode).comp
    (Procedure.second Nat.bits (prodCode Nat.bits ratCode))).comp e
  let get := Procedure.listGet pairCode (0,0)
  exact (tableProgram.comp env).pair ((get.comp (a.pair ps)).pair (get.comp (b.pair ps)))

noncomputable opaque routeProgram : Procedure (prodCode inputCode bondCode)
    (listCode pairCode) (fun x => QuantumRouteSelectorProgram.value (routeInput x.1 x.2)) :=
  QuantumRouteSelectorProgram.program.comp routeInputProgram

noncomputable opaque mapPathsProgram : Procedure (prodCode inputCode (listCode bondCode))
    (listCode (listCode pairCode))
    (fun x => x.2.map (fun e => QuantumRouteSelectorProgram.value (routeInput x.1 e))) :=
  Procedure.listMapWith (f := fun x e => QuantumRouteSelectorProgram.value (routeInput x e))
    zeroBond [] routeProgram

noncomputable opaque pathsProgram : Procedure inputCode (listCode (listCode pairCode)) paths :=
  (mapPathsProgram.comp ((Procedure.identity inputCode).pair mergedProgram)).congrFun
    (by intro x; rfl)

noncomputable opaque program : Procedure inputCode outputCode value :=
  (nProgram.pair (mergedProgram.pair constantProgram)).pair (positionsProgram.pair pathsProgram)

end ContinuumCoulomb.QuantumPlanarTapeProgram

end

end OAI
