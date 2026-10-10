import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumFiniteMembership
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumCellPathProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRetainedRoutes

namespace OAI

/-! Finite source cells, internal visits and crossing cells determine every
routing permission. These tests inspect finite encoded lists, including both
orientations of each internal port pair. -/

noncomputable section
namespace ContinuumCoulomb.QuantumRoutingTable
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode QuantumFiniteMembership

abbrev Visit := Pair × Pair
abbrev Table := List Pair × (List Visit × List Pair)
def visitCode : Visit → List Bool := prodCode pairCode pairCode
def tableCode : Table → List Bool :=
  prodCode (listCode pairCode) (prodCode (listCode visitCode) (listCode pairCode))
def inputCode : (Table × Pair) → List Bool := prodCode tableCode pairCode

def allowed (t : Table) : QMACellRouteBody → Bool
  | .ray p _ => decide (p ∈ t.1) && !decide (p ∈ t.2.2)
  | .pair p e => !decide (p ∈ t.2.2) &&
      decide ((p,((qmaCellPairLeft e).val,(qmaCellPairRight e).val)) ∈ t.2.1)
  | .patch p _ => decide (p ∈ t.2.2)
  | .corridor p a b c => decide (b = decide (p ∈ t.2.2)) &&
      decide (c = decide (qmaGridNeighbor p a ∈ t.2.2))

noncomputable opaque cellProgram : Procedure inputCode pairCode Prod.snd := Procedure.second _ _
noncomputable opaque tableProgram : Procedure inputCode tableCode Prod.fst := Procedure.first _ _
noncomputable opaque sourcesProgram : Procedure inputCode (listCode pairCode) (fun x => x.1.1) :=
  (Procedure.first _ _).comp tableProgram
noncomputable opaque visitsProgram : Procedure inputCode (listCode visitCode) (fun x => x.1.2.1) :=
  (Procedure.first _ _).comp ((Procedure.second _ _).comp tableProgram)
noncomputable opaque crossingsProgram : Procedure inputCode (listCode pairCode) (fun x => x.1.2.2) :=
  (Procedure.second _ _).comp ((Procedure.second _ _).comp tableProgram)
noncomputable opaque crossingProgram : Procedure inputCode Procedure.boolCode
    (fun x => decide (x.2 ∈ x.1.2.2)) := pairMemberProgram.comp (cellProgram.pair crossingsProgram)

noncomputable opaque rayAllowedProgram (a : Fin 4) : Procedure inputCode Procedure.boolCode
    (fun x => allowed x.1 (.ray x.2 a)) :=
  Procedure.boolAnd.comp ((pairMemberProgram.comp (cellProgram.pair sourcesProgram)).pair
    (Procedure.boolNot.comp crossingProgram))

noncomputable opaque pairAllowedProgram (e : Fin 6) : Procedure inputCode Procedure.boolCode
    (fun x => allowed x.1 (.pair x.2 e)) := by
  let memp := memberProgram visitCode ((0,0),(0,0)) (Procedure.prodEq pairEqProgram pairEqProgram)
  let v := cellProgram.pair (Procedure.constant inputCode pairCode
    ((qmaCellPairLeft e).val,(qmaCellPairRight e).val))
  exact Procedure.boolAnd.comp ((Procedure.boolNot.comp crossingProgram).pair
    (memp.comp (v.pair visitsProgram)))

noncomputable opaque patchAllowedProgram (e : Fin 9) : Procedure inputCode Procedure.boolCode
    (fun x => allowed x.1 (.patch x.2 e)) := crossingProgram

noncomputable opaque corridorAllowedProgram (a : Fin 4) (b c : Bool) :
    Procedure inputCode Procedure.boolCode (fun x => allowed x.1 (.corridor x.2 a b c)) := by
  let eqb := Procedure.ofBool Procedure.boolCode (fun x => decide (b=x))
  let eqc := Procedure.ofBool Procedure.boolCode (fun x => decide (c=x))
  let next := pairMemberProgram.comp
    ((QuantumCellPathProgram.neighborProgram a |>.comp cellProgram).pair crossingsProgram)
  exact Procedure.boolAnd.comp ((eqb.comp crossingProgram).pair (eqc.comp next))

end ContinuumCoulomb.QuantumRoutingTable

end

end OAI
