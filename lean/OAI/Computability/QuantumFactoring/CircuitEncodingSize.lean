import Mathlib
import OAI.Computability.QuantumFactoring.Basic

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring

lemma natWord_length (k : ℕ) : (natWord k).length=k+1 := by
  simp [natWord]

lemma Gate.arity_le (g : Gate) : g.arity≤4 := by
  rcases g with ⟨p,i,c⟩
  cases p <;> cases c <;> cases i <;> decide
lemma Primitive.code_le (p : Primitive) : p.code≤4 := by
  cases p <;> decide

lemma flatMap_length_bound {α β : Type*} (xs : List α) (f : α→List β) (b : ℕ)
    (h : ∀ x∈xs, (f x).length≤b) : (xs.flatMap f).length≤xs.length*b := by
  induction xs with
  | nil=>simp
  | cons x xs ih=>
    have hx:=h x (List.mem_cons_self)
    have ht:=ih (fun y hy=>h y (List.mem_cons_of_mem _ hy))
    simp only [List.flatMap_cons,List.length_append,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

/-- Addresses are unary in the frozen interface; bounded gate arity ensures
this encoding itself has only polynomial overhead in width and gate count. -/
lemma Instruction.encode_length {q : ℕ} (o : Instruction q) :
    o.encode.length≤7+4*q := by
  have h:=flatMap_length_bound (List.ofFn (fun i=> (o.wire i).val)) natWord q (by
    intro x hx
    obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hx
    rw [natWord_length]
    exact (o.wire i).isLt)
  rw [List.length_ofFn] at h
  have ha:=Nat.mul_le_mul_right q (Gate.arity_le o.gate)
  have hc:=Primitive.code_le o.gate.primitive
  simp only [Instruction.encode,List.length_append,natWord_length,List.length_cons,List.length_nil]
  omega

lemma Circuit.encode_length (c : Circuit) :
    c.encode.length≤c.qubits+2+c.instructions.length*(8+4*c.qubits) := by
  have h:=flatMap_length_bound c.instructions Instruction.encode (7+4*c.qubits)
    (fun x _=>Instruction.encode_length x)
  simp only [Circuit.encode,List.length_append,natWord_length]
  nlinarith

end ExactQuantumFactoring




end



end OAI
