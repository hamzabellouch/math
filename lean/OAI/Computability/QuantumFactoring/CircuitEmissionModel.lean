import Mathlib
import OAI.Computability.QuantumFactoring.RegisterCircuit
import OAI.Computability.QuantumFactoring.BitStackListCode
import OAI.Computability.QuantumFactoring.BitStackNaturals

namespace OAI



section

namespace ExactQuantumFactoring.CircuitEmission
structure Op where
  gate : Gate
  wires : List ℕ

def eraseOp {q : ℕ} (o : Instruction q) : Op:=⟨o.gate,List.ofFn (fun i=>(o.wire i).val)⟩
def Op.encode (o : Op) : List Bool:=
  natWord o.gate.primitive.code++[o.gate.inverse,o.gate.controlled]++o.wires.flatMap natWord
lemma eraseOp_encode {q : ℕ} (o : Instruction q) : (eraseOp o).encode=o.encode := rfl

def Op.map (f : ℕ→ℕ) (o : Op) : Op:=⟨o.gate,o.wires.map f⟩
def Op.reverse (o : Op) : Op:=⟨o.gate.reverse,o.wires⟩
lemma eraseOp_place {q r : ℕ} (w : Register q r) (o : Instruction q) (f : ℕ→ℕ)
    (h : ∀i,(w i).val=f i.val) : eraseOp (o.place w)=(eraseOp o).map f := by
  simp only [eraseOp,Instruction.place,Op.map,List.map_ofFn,Function.comp_apply,h]
  rfl
lemma eraseOp_reverse {q : ℕ} (o : Instruction q) : eraseOp o.reverse=(eraseOp o).reverse := rfl

structure Data where
  qubits : ℕ
  ops : List Op

def erase (c : Circuit) : Data:=⟨c.qubits,c.instructions.map eraseOp⟩
def Data.encode (c : Data) : List Bool:=natWord c.qubits++natWord c.ops.length++c.ops.flatMap Op.encode
lemma erase_encode (c : Circuit) : (erase c).encode=c.encode := by
  simp only [erase,Data.encode,Circuit.encode,List.length_map,List.flatMap_map,eraseOp_encode]

def primitiveCode (p : Primitive) : List Bool:=BitStackProgram.unaryCode p.code
def gateView (g : Gate):= (g.primitive,g.inverse,g.controlled)
def gatePayload:=BitStackProgram.prodCode primitiveCode
  (BitStackProgram.prodCode BitStackProgram.Procedure.boolCode BitStackProgram.Procedure.boolCode)
def gateCode (g : Gate) : List Bool:=gatePayload (gateView g)
def opView (o : Op):=(o.gate,o.wires)
def opPayload:=BitStackProgram.prodCode gateCode (BitStackProgram.listCode Nat.bits)
def opCode (o : Op) : List Bool:=opPayload (opView o)
def dataView (c : Data):=(c.qubits,c.ops)
def dataPayload:=BitStackProgram.prodCode BitStackProgram.unaryCode (BitStackProgram.listCode opCode)
def dataCode (c : Data) : List Bool:=dataPayload (dataView c)

def Op.encodeClipped (cap : ℕ) (o : Op) : List Bool:=
  natWord o.gate.primitive.code++[o.gate.inverse,o.gate.controlled]++
    o.wires.flatMap (fun i=>natWord (min cap i))
def Data.encodeClipped (c : Data) : List Bool:=natWord c.qubits++natWord c.ops.length++
  c.ops.flatMap (Op.encodeClipped c.qubits)
lemma eraseOp_encodeClipped {q : ℕ} (o : Instruction q) :
    (eraseOp o).encodeClipped q=o.encode := by
  unfold Op.encodeClipped eraseOp Instruction.encode
  congr 1
  apply List.flatMap_congr
  intro i hi
  obtain ⟨j,rfl⟩:=List.mem_ofFn.mp hi
  rw [min_eq_right (Nat.le_of_lt (o.wire j).isLt)]
lemma erase_encodeClipped (c : Circuit) : (erase c).encodeClipped=c.encode := by
  simp only [erase,Data.encodeClipped,Circuit.encode,List.length_map,List.flatMap_map,
    eraseOp_encodeClipped]
end ExactQuantumFactoring.CircuitEmission

end



end OAI
