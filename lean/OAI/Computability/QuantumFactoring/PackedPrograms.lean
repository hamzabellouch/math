import Mathlib
import OAI.Computability.QuantumFactoring.RegisterEncoded
import OAI.Computability.QuantumFactoring.OracleLayout

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open BooleanNetwork

def firstRegister (n m r : ℕ) : Register n (n+m+r) where
  toFun i := ⟨i.val,by omega⟩
  inj' := by
    intro i j h
    apply Fin.ext
    exact congrArg (fun t : Fin (n+m+r) => t.val) h

lemma packed_first {n m r : ℕ} (x : Basis n) (y : Basis m) :
    packed r x y ∘ firstRegister n m r = x := by
  funext i
  exact packed_input x y i

lemma packed_injective {n m r : ℕ} (y : Basis m) :
    Function.Injective (fun x : Basis n => packed r x y) := by
  intro x z h
  have hh := congrArg (fun t => t ∘ firstRegister n m r) h
  simpa only [packed_first] using hh

lemma packed_replace_first {n m r : ℕ} (x u : Basis n) (y : Basis m) :
    (firstRegister n m r).replace (packed r x y) u = packed r u y := by
  funext i
  by_cases hi : i.val<n
  · have he : i = firstRegister n m r ⟨i.val,hi⟩ := rfl
    rw [he, Register.replace_inside]
    exact (packed_input u y ⟨i.val,hi⟩).symm
  · have hout : ∀ j : Fin n, firstRegister n m r j ≠ i := by
      intro j he
      have hh := congrArg Fin.val he
      change j.val = i.val at hh
      omega
    rw [Register.replace_outside _ _ _ ⟨i,hout⟩]
    simp [packed,hi]

def firstProgram {n : ℕ} (m r : ℕ) (ops : List (Instruction n)) :
    List (Instruction (n+m+r)) := ops.map (Instruction.place (firstRegister n m r))

lemma firstProgram_length {n : ℕ} (m r : ℕ) (ops : List (Instruction n)) :
    (firstProgram m r ops).length = ops.length := by simp [firstProgram]

lemma firstProgram_state {n m r : ℕ} (ops : List (Instruction n)) (y : Basis m)
    (ψ : State n) :
    (programMatrix (firstProgram m r ops)).mulVec (encodeState (fun x => packed r x y) ψ) =
      encodeState (fun x => packed r x y) ((programMatrix ops).mulVec ψ) := by
  refine matrix_encodeState (fun x => packed r x y) (fun x => packed r x y)
    (programMatrix (firstProgram m r ops)) (programMatrix ops) ?_ ψ
  intro x
  rw [firstProgram, Register.placed_basis_state, packed_first]
  have he : (fun u => (firstRegister n m r).replace (packed r x y) u) =
      (fun u => packed r u y) := funext (fun u => packed_replace_first x u y)
  exact congrArg₂ (fun (e : Basis n → Basis (n+m+r)) (v : State n) => encodeState e v)
    he (matrix_basisVector (programMatrix ops) x)

lemma firstProgram_basis {n m r : ℕ} (ops : List (Instruction n)) (y : Basis m)
    (x : Basis n) :
    (programMatrix (firstProgram m r ops)).mulVec (basisVector (packed r x y)) =
      encodeState (fun z => packed r z y) ((programMatrix ops).mulVec (basisVector x)) := by
  rw [← encodeState_basis (fun z => packed r z y) x]
  exact firstProgram_state ops y _

lemma BooleanNetwork.oracleOn_state {n m r : ℕ} (c : BooleanNetwork n m)
    (hr : c.net.count ≤ r) (ψ : State n) :
    (programMatrix (oracleOn c hr)).mulVec
      (encodeState (fun x => packed r x (fun _ => false)) ψ) =
      encodeState (fun x => packed r x (c.eval x)) ψ := by
  classical
  rw [encodeState, Matrix.mulVec_sum]
  simp only [Matrix.mulVec_smul, oracleOn_basis, Bool.false_xor]
  rfl

end ExactQuantumFactoring


end

end OAI
