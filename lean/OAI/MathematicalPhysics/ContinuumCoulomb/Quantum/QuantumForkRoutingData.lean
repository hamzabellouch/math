import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkGridInitial
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkListSpatialPackage
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRoutingInputActual

namespace OAI

/-! A literal routing-input tape from the full fork state. Active-star bonds
are retained, and each anchor is the integer midpoint of its endpoint cells. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkRoutingData
open ExactQuantumFactoring.BitStackProgram QuantumForkList MediatorListProgram

def star (x : ℕ × Port) : Bond := (x.1,x.2.1,x.2.2)

noncomputable def starProgram : Procedure (prodCode Nat.bits portCode) bondCode star :=
  Procedure.identity bondCode

noncomputable def starBondsProgram :
    Procedure (prodCode unaryCode groupsCode) (listCode bondCode)
      (fun x => starBonds x.1 (groupAt x.2 x.1)) := by
  let i := Procedure.unaryToBits.comp (Procedure.first unaryCode groupsCode)
  let ps := groupAtProgram
  exact ((Procedure.listMapWith (f := fun i p => star (i,p)) (0,0) (0,0,0) starProgram).comp
    (i.pair ps)).congrFun (by intro x; rfl)

noncomputable def activeProgram : Procedure groupsCode (listCode bondCode) activeBonds := by
  let count := ExactQuantumFactoring.NativeAIG.Emission.listUnaryLength (listCode portCode) []
  let blocks := (Procedure.tabulate (f := fun gs i => starBonds i (groupAt gs i)) []
    starBondsProgram).comp (count.pair (Procedure.identity groupsCode))
  exact (QuantumRawExchange.flattenProgram bondCode (0,0,0)).comp blocks

noncomputable def fullProgram : Procedure stateCode (listCode bondCode) fullList :=
  (Procedure.listAppend bondCode (0,0,0)).comp
    (bondsProgram.pair (activeProgram.comp groupsProgram))

def endpoint (b : Bond) : QuantumRouteCode.Pair := (b.1,b.2.1)

noncomputable def endpointProgram : Procedure bondCode QuantumRouteCode.pairCode endpoint :=
  (Procedure.first Nat.bits (prodCode Nat.bits ratCode)).pair
    ((Procedure.first Nat.bits ratCode).comp (Procedure.second Nat.bits (prodCode Nat.bits ratCode)))

abbrev Query := Bond × List QuantumRouteCode.Pair
def queryCode : Query → List Bool := prodCode bondCode (listCode QuantumRouteCode.pairCode)

def anchor (x : Query) : QuantumRouteCode.Pair := QuantumGridMidpoint.value
  (QuantumForkGridProgram.lookup x.2 x.1.1,QuantumForkGridProgram.lookup x.2 x.1.2.1)

noncomputable def anchorProgram : Procedure queryCode QuantumRouteCode.pairCode anchor := by
  let b := Procedure.first bondCode (listCode QuantumRouteCode.pairCode)
  let cells := Procedure.second bondCode (listCode QuantumRouteCode.pairCode)
  let ends := endpointProgram.comp b
  let left := (Procedure.first Nat.bits Nat.bits).comp ends
  let right := (Procedure.second Nat.bits Nat.bits).comp ends
  let get := Procedure.listGet QuantumRouteCode.pairCode (0,0)
  exact QuantumGridMidpoint.program.comp
    ((get.comp (left.pair cells)).pair (get.comp (right.pair cells)))

def value (x : QuantumForkGridProgram.Cells) : QuantumRoutingInputProgram.Data :=
  ((x.2,(fullList x.1).map (fun b => anchor (b,x.2))),
    (fullList x.1).map endpoint)

noncomputable def program : Procedure QuantumForkGridProgram.cellsCode
    QuantumRoutingInputProgram.dataCode value := by
  let state := Procedure.first stateCode (listCode QuantumRouteCode.pairCode)
  let cells := Procedure.second stateCode (listCode QuantumRouteCode.pairCode)
  let bonds := fullProgram.comp state
  let anchorWith := anchorProgram.comp
    ((Procedure.second (listCode QuantumRouteCode.pairCode) bondCode).pair
      (Procedure.first (listCode QuantumRouteCode.pairCode) bondCode))
  let anchors := (Procedure.listMapWith
    (f := fun cells b => anchor (b,cells)) (0,0,0) (0,0) anchorWith).comp (cells.pair bonds)
  let ends := (Procedure.listMap (0,0,0) (0,0) endpointProgram).comp bonds
  exact (cells.pair anchors).pair ends

private theorem lookup_ofFn {n : ℕ} (f : Fin n → QuantumRouteCode.Pair) (i : Fin n) :
    QuantumForkGridProgram.lookup (List.ofFn f) i.val=f i :=
  QuantumOrdinalProgram.lookup_ofFn f i

theorem value_spatialModel {rows width : ℕ} (s : State)
    (hs : ValidPorts s.1 s.2.2.2) (hb : SourceBondLists.bounded s.1 s.2.1)
    (hn : ∀ b ∈ s.2.1, b.1≠b.2.1) (cell : ℕ → QMAGridCell rows width) (A : ℕ)
    (hc : ∀ p, qmaCellMass (fun v : Fin s.1 => cell v.val) p ≤ A)
    (hd : ∀ v : Fin s.1, degree (fullList s) v.val ≤ 3)
    (hl : BondLocal (fullList s) cell CommonCell) :
    value (s,List.ofFn (fun v : Fin s.1 => ((cell v.val).1.val,(cell v.val).2.val))) =
      QuantumRoutingInputProgram.actualData (spatialModel s hs hb hn cell A hc hd hl)
        (Equiv.refl _) := by
  let G := fullGraph s hs hb hn
  let cells : Fin s.1 → QuantumRouteCode.Pair :=
    fun v => ((cell v.val).1.val,(cell v.val).2.val)
  have endpoints : (fullList s).map endpoint =
      List.ofFn (fun i : Fin (fullList s).length => endpoint ((fullList s).get i)) := by
    simpa only [List.get_eq_getElem] using
      (List.ofFn_getElem_eq_map (fullList s) endpoint).symm
  have anchors : (fullList s).map (fun b => anchor (b,List.ofFn cells)) =
      List.ofFn (fun i : Fin (fullList s).length =>
        QuantumGridMidpoint.value (cells (G.left i),cells (G.right i))) := by
    rw [← List.ofFn_getElem_eq_map (fullList s) (fun b => anchor (b,List.ofFn cells))]
    apply congrArg List.ofFn
    funext i
    change QuantumGridMidpoint.value
      (QuantumForkGridProgram.lookup (List.ofFn cells) (G.left i).val,
        QuantumForkGridProgram.lookup (List.ofFn cells) (G.right i).val) = _
    dsimp only [G,fullGraph,QuantumListGraph.ofBonds]
    rw [lookup_ofFn,lookup_ofFn]
  unfold value QuantumRoutingInputProgram.actualData
  apply congrArg₂ Prod.mk
  · apply congrArg₂ Prod.mk
    · rfl
    · exact anchors
  · exact endpoints

end ContinuumCoulomb.QuantumForkRoutingData

end

end OAI
