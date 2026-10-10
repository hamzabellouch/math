import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumSpatialPortProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumDistinctCrossings
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRoutingFamily
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumCrossingCompiled
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumCrossingSiteProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumCrossingPositionProgram

namespace OAI

/-! A literal composition from the prepared spatial input to the crossing
Hamiltonian, its physical positions, and the finite routing permission table. -/

noncomputable section
namespace ContinuumCoulomb.QuantumSpatialCrossingProgram
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode
open QuantumForkList (spatialDensity)

abbrev Input := QuantumSpatialPortProgram.Input
def inputCode : Input → List Bool := QuantumSpatialPortProgram.inputCode
abbrev Output := (QuantumListPathStep.Output × List Pair) × QuantumRoutingTable.Table
def outputCode : Output → List Bool :=
  prodCode (prodCode QuantumListPathStep.outputCode (listCode pairCode))
    QuantumRoutingTable.tableCode

def coarse (A D : ℕ) (x : Input) : QuantumPathTable.Input :=
  QuantumRoutingFamily.table (spatialDensity A D) (27*spatialDensity A D)
    (QuantumForkRoutingData.value (QuantumForkGridProgram.output D x.2))
def cells (A D : ℕ) (x : Input) : List Pair := QuantumDistinctCrossings.value (coarse A D x)
def table (A D : ℕ) (x : Input) : QuantumRoutingTable.Table := QuantumPathTable.compile (coarse A D x)
def oldPositions (A D : ℕ) (x : Input) : List Pair := (QuantumSpatialPortProgram.value A D x).2.1
def oldPacket (A D : ℕ) (x : Input) : QuantumListPathStep.Output :=
  let s := (QuantumSpatialPortProgram.value A D x).1
  (s.1,QuantumListSchedule.erase s.2.2,s.2.1)
def sites (A D : ℕ) (x : Input) : List QuantumCrossingListBlock.Sites :=
  QuantumCrossingSiteProgram.allSites (oldPositions A D x,cells A D x)
def crossingInput (A D : ℕ) (x : Input) : QuantumCrossingListLayer.Input :=
  QuantumCrossingSelectProgram.value (x.1,oldPacket A D x,sites A D x)
def positions (A D : ℕ) (x : Input) : List Pair :=
  QuantumCrossingPositionProgram.positions (cells A D x,oldPositions A D x)
def value (A D : ℕ) (x : Input) : Output :=
  ((QuantumCrossingListLayer.value (crossingInput A D x),positions A D x),table A D x)

noncomputable opaque coarseProgram (A D : ℕ) :
    Procedure inputCode QuantumPathTable.inputCode (coarse A D) :=
  (QuantumRoutingFamily.tableProgram (spatialDensity A D) (27*spatialDensity A D)).comp
    (QuantumForkRoutingData.program.comp ((QuantumForkGridProgram.outputProgram D).comp
      (Procedure.second ratCode QuantumForkGridProgram.preparedCode)))
noncomputable opaque cellsProgram (A D : ℕ) :
    Procedure inputCode (listCode pairCode) (cells A D) :=
  QuantumDistinctCrossings.program.comp (coarseProgram A D)
noncomputable opaque tableProgram (A D : ℕ) :
    Procedure inputCode QuantumRoutingTable.tableCode (table A D) :=
  QuantumPathTable.compileProgram.comp (coarseProgram A D)
noncomputable opaque oldPositionsProgram (A D : ℕ) :
    Procedure inputCode (listCode pairCode) (oldPositions A D) :=
  ((Procedure.first (listCode pairCode) (listCode (listCode pairCode))).comp
    (Procedure.second QuantumListSchedule.stateCode
      (prodCode (listCode pairCode) (listCode (listCode pairCode))))).comp
        (QuantumSpatialPortProgram.program A D)
noncomputable opaque oldPacketProgram (A D : ℕ) :
    Procedure inputCode QuantumListPathStep.outputCode (oldPacket A D) := by
  let s := (Procedure.first QuantumListSchedule.stateCode
    (prodCode (listCode pairCode) (listCode (listCode pairCode)))).comp
      (QuantumSpatialPortProgram.program A D)
  let n := (Procedure.first unaryCode
    (prodCode ratCode (listCode QuantumListSchedule.entryCode))).comp s
  let rest := (Procedure.second unaryCode
    (prodCode ratCode (listCode QuantumListSchedule.entryCode))).comp s
  let c := (Procedure.first ratCode (listCode QuantumListSchedule.entryCode)).comp rest
  let bs := QuantumListSchedule.eraseProgram.comp
    ((Procedure.second ratCode (listCode QuantumListSchedule.entryCode)).comp rest)
  exact n.pair (bs.pair c)
noncomputable opaque sitesProgram (A D : ℕ) :
    Procedure inputCode (listCode QuantumCrossingListBlock.sitesCode) (sites A D) :=
  QuantumCrossingSiteProgram.allSitesProgram.comp
    ((oldPositionsProgram A D).pair (cellsProgram A D))
noncomputable opaque crossingInputProgram (A D : ℕ) :
    Procedure inputCode QuantumCrossingListLayer.inputCode (crossingInput A D) :=
  QuantumCrossingSelectProgram.program.comp
    ((Procedure.first ratCode QuantumForkGridProgram.preparedCode).pair
      ((oldPacketProgram A D).pair (sitesProgram A D)))
noncomputable opaque positionsProgram (A D : ℕ) :
    Procedure inputCode (listCode pairCode) (positions A D) :=
  QuantumCrossingPositionProgram.positionsProgram.comp
    ((cellsProgram A D).pair (oldPositionsProgram A D))
noncomputable opaque program (A D : ℕ) : Procedure inputCode outputCode (value A D) :=
  ((QuantumCrossingListLayer.program.comp (crossingInputProgram A D)).pair
    (positionsProgram A D)).pair (tableProgram A D)

end ContinuumCoulomb.QuantumSpatialCrossingProgram

end

end OAI
