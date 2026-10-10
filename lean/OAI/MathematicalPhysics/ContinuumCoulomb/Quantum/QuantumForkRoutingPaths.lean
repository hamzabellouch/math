import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkRoutingData
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPortChainActual

namespace OAI

/-! The full fork-state tape computes the physical port chains used by the
ordinal spatial model, without an oracle for cells or intermediate routes. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkRoutingPaths
open QuantumForkList ExactQuantumFactoring.BitStackProgram

abbrev Input := ℕ × QuantumForkGridProgram.Cells
def inputCode : Input → List Bool := prodCode unaryCode QuantumForkGridProgram.cellsCode

def value (A B : ℕ) (x : Input) : List QuantumRouteCode.Pair :=
  QuantumPortChainProgram.routed A B (x.1,QuantumForkRoutingData.value x.2)

noncomputable def program (A B : ℕ) : Procedure inputCode
    (listCode QuantumRouteCode.pairCode) (value A B) :=
  (QuantumPortChainProgram.routedProgram A B).comp
    ((Procedure.first unaryCode QuantumForkGridProgram.cellsCode).pair
      (QuantumForkRoutingData.program.comp (Procedure.second unaryCode QuantumForkGridProgram.cellsCode)))

theorem value_spatialModel {rows width : ℕ} (s : State)
    (hs : ValidPorts s.1 s.2.2.2) (hb : SourceBondLists.bounded s.1 s.2.1)
    (hn : ∀ b ∈ s.2.1, b.1≠b.2.1) (cell : ℕ → QMAGridCell rows width) (A : ℕ)
    (hc : ∀ p, qmaCellMass (fun v : Fin s.1 => cell v.val) p ≤ A)
    (hd : ∀ v : Fin s.1, degree (fullList s) v.val ≤ 3)
    (hl : BondLocal (fullList s) cell CommonCell) (hA : 0 < A)
    (hg : ∀ v, qmaGraphDegree (spatialModel s hs hb hn cell A hc hd hl).left
      (spatialModel s hs hb hn cell A hc hd hl).right v ≤ 3)
    (e : Fin (fullList s).length) :
    let M := (spatialModel s hs hb hn cell A hc hd hl).withOrdinalSlots (Equiv.refl _)
    value A (27*A) (e.val,(s,List.ofFn
      (fun v : Fin s.1 => ((cell v.val).1.val,(cell v.val).2.val)))) =
        (List.range (2*M.coarseLength hg e+2)).map
          (qmaPortChain (M.coarseRoute hg e) (M.coarseLength hg e)) := by
  dsimp only
  unfold value
  rw [QuantumForkRoutingData.value_spatialModel s hs hb hn cell A hc hd hl]
  exact QuantumPortChainProgram.routed_actual
    (spatialModel s hs hb hn cell A hc hd hl) (Equiv.refl _) hA hg e

end ContinuumCoulomb.QuantumForkRoutingPaths

end

end OAI
