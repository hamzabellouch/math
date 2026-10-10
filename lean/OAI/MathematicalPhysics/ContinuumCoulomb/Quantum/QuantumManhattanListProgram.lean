import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRouteProgram
import OAI.Computability.QuantumFactoring.BitStackBoundedUnary
import OAI.Computability.QuantumFactoring.BitStackTabulate

namespace OAI

/-! Enumerate the Manhattan segment with an explicit fixed route budget.
The cap makes enumeration polynomial on every input, and disappears for
the spatial routes satisfying the proved length bound. -/

noncomputable section
namespace ContinuumCoulomb.QuantumManhattanListProgram
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode

abbrev Ends := Pair × Pair
def endsCode : Ends → List Bool := prodCode pairCode pairCode

def value (K : ℕ) (x : Ends) : List Pair :=
  (List.range (min K (qmaManhattanLength x.1 x.2)+1)).map (qmaManhattanPoint x.1 x.2)

noncomputable def distanceProgram : Procedure endsCode Nat.bits
    (fun x => qmaManhattanLength x.1 x.2) :=
  QuantumRouteCode.lengthProgram.comp
    ((Procedure.identity endsCode).pair (Procedure.constant endsCode Nat.bits 0))

noncomputable def program (K : ℕ) : Procedure endsCode (listCode pairCode) (value K) := by
  let length := Procedure.clippedUnary.comp
    ((Procedure.constant endsCode unaryCode K).pair distanceProgram)
  let point := QuantumRouteCode.pointProgram.comp
    ((Procedure.second unaryCode endsCode).pair
      (Procedure.unaryToBits.comp (Procedure.first unaryCode endsCode)))
  exact (Procedure.tabulate (f := fun x i => qmaManhattanPoint x.1 x.2 i) (0,0) point).comp
    ((Procedure.unarySuccessor.comp length).pair (Procedure.identity endsCode))

theorem value_exact (K : ℕ) (x : Ends) (h : qmaManhattanLength x.1 x.2 ≤ K) :
    value K x = (List.range (qmaManhattanLength x.1 x.2+1)).map (qmaManhattanPoint x.1 x.2) := by
  simp only [value,Nat.min_eq_right h]

end ContinuumCoulomb.QuantumManhattanListProgram

end

end OAI
