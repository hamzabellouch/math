import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumSpatialReference
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRoutingInputProgram

namespace OAI

/-! Integer midpoints choose a common neighboring cell deterministically.
Their coordinate map has a literal polynomial register program. -/

noncomputable section
namespace ContinuumCoulomb
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode

def qmaGridMidpoint {rows width : ℕ} (p q : QMAGridCell rows width) :
    QMAGridCell rows width :=
  (⟨(p.1.val+q.1.val)/2,by have := p.1.isLt; have := q.1.isLt; omega⟩,
   ⟨(p.2.val+q.2.val)/2,by have := p.2.isLt; have := q.2.isLt; omega⟩)

theorem qmaGridMidpoint_near {rows width : ℕ} (p q a : QMAGridCell rows width)
    (hp : QMAGridCellsNear p a) (hq : QMAGridCellsNear q a) :
    QMAGridCellsNear p (qmaGridMidpoint p q) ∧
      QMAGridCellsNear q (qmaGridMidpoint p q) := by
  rcases hp with ⟨hp₁,hp₂,hp₃,hp₄⟩
  rcases hq with ⟨hq₁,hq₂,hq₃,hq₄⟩
  unfold QMAGridCellsNear qmaGridMidpoint
  dsimp only
  omega

namespace QuantumGridMidpoint

def value (x : Pair × Pair) : Pair :=
  ((x.1.1+x.2.1)/2,(x.1.2+x.2.2)/2)

noncomputable def program : Procedure (prodCode pairCode pairCode) pairCode value := by
  let p := Procedure.first pairCode pairCode
  let q := Procedure.second pairCode pairCode
  let first := Procedure.first Nat.bits Nat.bits
  let second := Procedure.second Nat.bits Nat.bits
  let two := Procedure.constant (prodCode pairCode pairCode) Nat.bits 2
  let row := Procedure.binaryDiv.comp
    ((Procedure.binaryAdd.comp ((first.comp p).pair (first.comp q))).pair two)
  let col := Procedure.binaryDiv.comp
    ((Procedure.binaryAdd.comp ((second.comp p).pair (second.comp q))).pair two)
  exact row.pair col

theorem value_eq {rows width : ℕ} (p q : QMAGridCell rows width) :
    value ((p.1.val,p.2.val),(q.1.val,q.2.val)) =
      ((qmaGridMidpoint p q).1.val,(qmaGridMidpoint p q).2.val) := rfl

end QuantumGridMidpoint
end ContinuumCoulomb

end

end OAI
