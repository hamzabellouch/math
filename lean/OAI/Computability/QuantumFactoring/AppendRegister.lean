import Mathlib
import OAI.Computability.QuantumFactoring.RegisterEncoded

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators

def rightRegister (p q : ℕ) : Register q (p+q) := ⟨Fin.natAdd p, Fin.natAdd_injective q p⟩

lemma append_rightRegister {p q : ℕ} (x : Basis p) (y : Basis q) :
    Fin.append x y ∘ rightRegister p q = y := by
  funext i
  exact Fin.append_right _ _ i

lemma append_right_injective {p q : ℕ} (x : Basis p) :
    Function.Injective (Fin.append x : Basis q → Basis (p+q)) := by
  intro y z h
  have hh := congrArg (fun v => v ∘ rightRegister p q) h
  simpa only [append_rightRegister] using hh

lemma append_replace_right {p q : ℕ} (x : Basis p) (y z : Basis q) :
    (rightRegister p q).replace (Fin.append x y) z = Fin.append x z := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · have hj : ∀ k, rightRegister p q k ≠ j.castAdd q := by
      intro k h
      have hh := congrArg Fin.val h
      change p+k.val=j.val at hh
      have := j.isLt
      omega
    rw [Register.replace_outside _ _ _ ⟨j.castAdd q,hj⟩]
    simp only [Fin.append_left]
  · change (rightRegister p q).replace (Fin.append x y) z (rightRegister p q j) = _
    rw [Register.replace_inside,Fin.append_right]

def rightProgram {q : ℕ} (p : ℕ) (ops : List (Instruction q)) :
    List (Instruction (p+q)) := ops.map (Instruction.place (rightRegister p q))

lemma rightProgram_basis {p q : ℕ} (ops : List (Instruction q)) (x : Basis p) (y : Basis q) :
    (programMatrix (rightProgram p ops)).mulVec (basisVector (Fin.append x y)) =
      encodeState (Fin.append x) ((programMatrix ops).mulVec (basisVector y)) := by
  rw [rightProgram,Register.placed_basis_state,append_rightRegister]
  congr 1
  funext z
  exact append_replace_right x y z

lemma rightProgram_entry {p q : ℕ} (ops : List (Instruction q)) (x : Basis p) (y z : Basis q) :
    programMatrix (rightProgram p ops) (Fin.append x z) (Fin.append x y) =
      programMatrix ops z y := by
  have hh := congrFun (rightProgram_basis ops x y) (Fin.append x z)
  simpa only [encodeState_at _ (append_right_injective x),matrix_basisVector] using hh

end ExactQuantumFactoring


end

end OAI
