import Mathlib
import OAI.Computability.QuantumFactoring.InitialOrderState
import OAI.Computability.QuantumFactoring.PreparedOracle

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open BooleanNetwork

/-- A coherent fresh launch on an encoded old history. The local law refers
only to the actually computed Boolean initializer, never to a selected outcome. -/
lemma preparedOracle_encode {α β : Type*} [Fintype α] [Fintype β] {p q r : ℕ}
    (e : α→Basis p) (f : β→Basis q) (ψ : α→ℂ) (F : α→β→ℂ)
    (c : BooleanNetwork p q) (hc : c.net.count ≤ r) (ops : List (Instruction q))
    (hlocal : ∀ a,(programMatrix ops).mulVec (basisVector (c.eval (e a)))=encodeState f (F a)) :
    (programMatrix (preparedOracle c hc ops)).mulVec
      (encodeState (fun a=>packed r (e a) (fun _=>false)) ψ)=
    encodeState (fun ab : α×β=>packed r (e ab.1) (f ab.2)) (RecordedHistory.appendState ψ F) := by
  rw [encodeState,Matrix.mulVec_sum]
  simp only [Matrix.mulVec_smul,preparedOracle_basis,hlocal,encodeState_comp]
  unfold encodeState RecordedHistory.appendState
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [smul_smul]
  rfl

def appendPrepared {p q r : ℕ} (A : List (Instruction p)) (c : BooleanNetwork p q)
    (hc : c.net.count ≤ r) (ops : List (Instruction q)) : List (Instruction (p+q+r)) :=
  firstProgram q r A++preparedOracle c hc ops

lemma appendPrepared_length {p q r : ℕ} (A : List (Instruction p)) (c : BooleanNetwork p q)
    (hc : c.net.count ≤ r) (ops : List (Instruction q)) :
    (appendPrepared A c hc ops).length ≤ A.length+4*c.net.count+2*q+ops.length := by
  have h := preparedOracle_length c hc ops
  simp only [appendPrepared,List.length_append,firstProgram_length]
  omega

lemma appendPrepared_state {α β : Type*} [Fintype α] [Fintype β] {p q r : ℕ}
    (e : α→Basis p) (f : β→Basis q) (ψ : α→ℂ) (F : α→β→ℂ)
    (A : List (Instruction p)) (v : Basis p)
    (hA : (programMatrix A).mulVec (basisVector v)=encodeState e ψ)
    (c : BooleanNetwork p q) (hc : c.net.count ≤ r) (ops : List (Instruction q))
    (hlocal : ∀ a,(programMatrix ops).mulVec (basisVector (c.eval (e a)))=encodeState f (F a)) :
    (programMatrix (appendPrepared A c hc ops)).mulVec (basisVector (packed r v (fun _=>false)))=
      encodeState (fun ab : α×β=>packed r (e ab.1) (f ab.2)) (RecordedHistory.appendState ψ F) := by
  rw [appendPrepared,programMatrix_append,←Matrix.mulVec_mulVec,firstProgram_basis,hA,encodeState_comp]
  exact preparedOracle_encode e f ψ F c hc ops hlocal

end ExactQuantumFactoring


end

end OAI
