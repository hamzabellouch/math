import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumEndpointListProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumManhattanListProgram

namespace OAI

/-! Enumerate the bounded Manhattan portion of each actual buffered route.
The horizontal and vertical translations are literal binary arithmetic. -/

noncomputable section
namespace ContinuumCoulomb.QuantumSpacedListProgram
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode

def point (B color : ℕ) (p : Pair) : Pair :=
  qmaBufferedCellPoint (9*B+3) p (8*(color+3),8*(color+3))

abbrev PointInput := ℕ × Pair
def pointCode : PointInput → List Bool := prodCode unaryCode pairCode

noncomputable def pointProgram (B : ℕ) : Procedure pointCode pairCode
    (fun x => point B x.1 x.2) := by
  let color := Procedure.unaryToBits.comp (Procedure.first unaryCode pairCode)
  let port := Procedure.binaryMul.comp ((Procedure.constant pointCode Nat.bits 8).pair
    (Procedure.binaryAdd.comp (color.pair (Procedure.constant pointCode Nat.bits 3))))
  exact (QuantumEndpointListProgram.translateProgram B).comp
    ((Procedure.second unaryCode pairCode).pair (port.pair port))

abbrev Input := ℕ × (Pair × Pair)
def inputCode : Input → List Bool := prodCode unaryCode (prodCode pairCode pairCode)
def budget (A B : ℕ) : ℕ := 8*(9*B+9)*(3*A+2)
def value (A B : ℕ) (x : Input) : List Pair :=
  QuantumManhattanListProgram.value (budget A B) (point B x.1 x.2.1,point B x.1 x.2.2)

noncomputable def program (A B : ℕ) : Procedure inputCode (listCode pairCode) (value A B) := by
  let color := Procedure.first unaryCode (prodCode pairCode pairCode)
  let ends := Procedure.second unaryCode (prodCode pairCode pairCode)
  let left := (pointProgram B).comp (color.pair ((Procedure.first pairCode pairCode).comp ends))
  let right := (pointProgram B).comp (color.pair ((Procedure.second pairCode pairCode).comp ends))
  exact (QuantumManhattanListProgram.program (budget A B)).comp (left.pair right)

theorem point_actual {A B : ℕ} (M : QMASpatialExchangeModel A B) (e : M.Term) (p : Pair) :
    point B (M.laneColor e).val p = qmaLanePoint (M.spacedColor e) p := rfl

theorem value_actual {A B : ℕ} (M : QMASpatialExchangeModel A B) (e : M.Term) :
    value A B ((M.laneColor e).val,M.routeVertex (M.left e),M.routeVertex (M.right e)) =
      M.spacedList e := by
  unfold value
  rw [point_actual,point_actual,QuantumManhattanListProgram.value_exact]
  · rfl
  · exact M.spaced_length e

end ContinuumCoulomb.QuantumSpacedListProgram

end

end OAI
