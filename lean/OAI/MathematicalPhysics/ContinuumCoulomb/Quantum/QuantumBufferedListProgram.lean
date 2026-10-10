import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumSpacedListProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumWalkErasureProgram

namespace OAI

/-! Literal construction and loop erasure of the complete buffered route.
The input consists of two computed fine-grid endpoints, one lane color and
the two computed incident port ranks. -/

noncomputable section
namespace ContinuumCoulomb.QuantumBufferedListProgram
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode

abbrev Input := (Pair × Pair) × (ℕ × (ℕ × ℕ))
def inputCode : Input → List Bool :=
  prodCode (prodCode pairCode pairCode) (prodCode unaryCode (prodCode unaryCode unaryCode))

def value (A B : ℕ) (x : Input) : List Pair :=
  QuantumEndpointListProgram.value B (x.1.1,x.2.2.1,x.2.1) ++
    (QuantumSpacedListProgram.value A B (x.2.1,x.1.1,x.1.2)).tail ++
    (QuantumEndpointListProgram.value B (x.1.2,x.2.2.2,x.2.1)).reverse.tail

noncomputable def program (A B : ℕ) : Procedure inputCode (listCode pairCode) (value A B) := by
  let ends := Procedure.first (prodCode pairCode pairCode) (prodCode unaryCode (prodCode unaryCode unaryCode))
  let nums := Procedure.second (prodCode pairCode pairCode) (prodCode unaryCode (prodCode unaryCode unaryCode))
  let left := (Procedure.first pairCode pairCode).comp ends
  let right := (Procedure.second pairCode pairCode).comp ends
  let lane := (Procedure.first unaryCode (prodCode unaryCode unaryCode)).comp nums
  let ports := (Procedure.second unaryCode (prodCode unaryCode unaryCode)).comp nums
  let la := (Procedure.first unaryCode unaryCode).comp ports
  let ra := (Procedure.second unaryCode unaryCode).comp ports
  let leftArm := (QuantumEndpointListProgram.program B).comp (left.pair (la.pair lane))
  let rightArm := (QuantumEndpointListProgram.program B).comp (right.pair (ra.pair lane))
  let middle := (Procedure.listTail pairCode).comp
    ((QuantumSpacedListProgram.program A B).comp (lane.pair (left.pair right)))
  let last := (Procedure.listTail pairCode).comp ((Procedure.listReverse pairCode (0,0)).comp rightArm)
  let append := Procedure.listAppend pairCode (0,0)
  exact append.comp ((append.comp (leftArm.pair middle)).pair last)

def actualInput {A B : ℕ} (M : QMASpatialExchangeModel A B)
    (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3) (e : M.Term) : Input :=
  ((M.routeVertex (M.left e),M.routeVertex (M.right e)),
    (M.laneColor e).val,
    ((M.endpointPorts hd (M.left e)).assign ⟨e,Or.inl rfl⟩).val,
    ((M.endpointPorts hd (M.right e)).assign ⟨e,Or.inr rfl⟩).val)

theorem value_actual {A B : ℕ} (M : QMASpatialExchangeModel A B)
    (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3) (e : M.Term) :
    value A B (actualInput M hd e) = M.bufferedList hd e := by
  unfold value actualInput
  rw [QuantumEndpointListProgram.value_actual,QuantumSpacedListProgram.value_actual,
    QuantumEndpointListProgram.value_actual]
  rfl

def path (A B : ℕ) (x : Input) : List Pair := QuantumWalkErasure.erase (value A B x)

noncomputable def pathProgram (A B : ℕ) : Procedure inputCode (listCode pairCode) (path A B) :=
  QuantumWalkErasure.cellProgram.comp (program A B)

theorem path_actual {A B : ℕ} (M : QMASpatialExchangeModel A B)
    (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3) (e : M.Term) :
    path A B (actualInput M hd e) = (M.bufferedPath hd e).val.support := by
  rw [path,value_actual,M.bufferedPath_support_list]

end ContinuumCoulomb.QuantumBufferedListProgram

end

end OAI
