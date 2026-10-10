import Mathlib
import OAI.Computability.QuantumFactoring.CircuitEncodingSize
import OAI.Computability.QuantumFactoring.CircuitEmissionModel
import OAI.Computability.QuantumFactoring.EmissionCombinators

namespace OAI



section

namespace ExactQuantumFactoring.CircuitEmission
open BitStackProgram BitStackProgram.Emits
lemma gateCode_bound (g : Gate) : (gateCode g).length≤20:=by
  have h:=Primitive.code_le g.primitive
  simp only [gateCode,gatePayload,gateView,prodCode, pairBits_length,primitiveCode,unaryCode,List.length_replicate,
    Procedure.boolCode,List.length_cons,List.length_nil]
  omega
lemma opCode_bound {q : ℕ} (o : Instruction q) : (opCode (eraseOp o)).length≤100+16*q:=by
  have h:=NativeAIG.listCode_length_bound Nat.bits (List.ofFn (fun i=>(o.wire i).val)) q (by
    intro i hi
    obtain ⟨j,rfl⟩:=List.mem_ofFn.mp hi
    exact (NativeAIG.nat_bits_length_bound _).trans (Nat.le_of_lt (o.wire j).isLt))
  rw [List.length_ofFn] at h
  have hg:=gateCode_bound o.gate
  have ha:=Gate.arity_le o.gate
  change (prodCode gateCode (listCode Nat.bits) (o.gate,List.ofFn (fun i=>(o.wire i).val))).length≤_
  simp only [prodCode, pairBits_length]
  nlinarith
lemma opsCode_bound {q : ℕ} (p : List (Instruction q)) :
    (listCode opCode (p.map eraseOp)).length≤p.length*(202+32*q)+1:=by
  have h:=NativeAIG.listCode_length_bound opCode (p.map eraseOp) (100+16*q) (by
    intro o ho;obtain ⟨i,hi,rfl⟩:=List.mem_map.mp ho;exact opCode_bound i)
  simp only [List.length_map] at h
  nlinarith

end ExactQuantumFactoring.CircuitEmission
end

end OAI
