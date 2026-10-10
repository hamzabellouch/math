import Mathlib
import OAI.Computability.QuantumFactoring.AppendRegister
import OAI.Computability.QuantumFactoring.ControlledHadamard
import OAI.Computability.QuantumFactoring.BitArithmetic

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open Exactness BitArithmetic BooleanNetwork

lemma rightProgram_state {p q : ℕ} (ops : List (Instruction q)) (x : Basis p) (ψ : State q) :
    (programMatrix (rightProgram p ops)).mulVec (encodeState (fun y => Fin.append x y) ψ)=
      encodeState (fun y => Fin.append x y) ((programMatrix ops).mulVec ψ) := by
  apply matrix_encodeState
  intro y
  simpa only [matrix_basisVector] using rightProgram_basis ops x y

lemma encode_append_supported {p q : ℕ} (x : Basis p) (ψ : State q) (i : Fin p) :
    Supported (fun y : Basis (p+q) => y (i.castAdd q)=x i)
      (encodeState (fun y => Fin.append x y) ψ) := by
  intro y hy
  apply encodeState_outside
  rintro ⟨z,rfl⟩
  exact hy (Fin.append_left _ _ _)

def maskGate (n : ℕ) (j : Fin n) : Instruction (n+n) :=
  controlledHadamardAt (j.castAdd n) (Fin.natAdd n j) (by
    intro hh
    have he := congrArg Fin.val hh
    simp only [Fin.val_castAdd,Fin.val_natAdd] at he
    have := j.isLt
    omega)

lemma maskGate_state (n : ℕ) (j : Fin n) (mask : Basis n) (ψ : State n) :
    (maskGate n j).matrix.mulVec (encodeState (fun y => Fin.append mask y) ψ)=
      encodeState (fun y => Fin.append mask y)
        (if mask j then (hadamardAt j).matrix.mulVec ψ else ψ) := by
  rw [maskGate,controlledHadamardAt_sector _ _ _ (mask j) _ (encode_append_supported mask ψ j)]
  cases hj : mask j
  · rfl
  · have he : (hadamardAt j).place (rightRegister n n)=hadamardAt (Fin.natAdd n j) := rfl
    have hh := rightProgram_state [hadamardAt j] mask ψ
    simpa only [rightProgram,List.map_cons,List.map_nil,he,programMatrix_singleton,ite_true] using hh

def maskedPrefix (n : ℕ) : (k : ℕ)→k ≤ n→List (Instruction (n+n))
  | 0,_ => []
  | k+1,h => maskedPrefix n k (by omega)++[maskGate n ⟨k,by omega⟩]

def selectedPrefix {n : ℕ} (mask : Basis n) : (k : ℕ)→k ≤ n→List (Instruction n)
  | 0,_ => []
  | k+1,h => selectedPrefix mask k (by omega)++
      (if mask ⟨k,by omega⟩ then [hadamardAt ⟨k,by omega⟩] else [])

lemma maskedPrefix_length (n k : ℕ) (h : k ≤ n) : (maskedPrefix n k h).length=k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [maskedPrefix,List.length_append,List.length_singleton,ih]

/-- The mask is ordinary retained input data. This equation is valid before
any measurement and for arbitrary coherent states in the target register. -/
lemma maskedPrefix_state (n k : ℕ) (h : k ≤ n) (mask : Basis n) (ψ : State n) :
    (programMatrix (maskedPrefix n k h)).mulVec (encodeState (fun y => Fin.append mask y) ψ)=
      encodeState (fun y => Fin.append mask y) ((programMatrix (selectedPrefix mask k h)).mulVec ψ) := by
  induction k with
  | zero => simp only [maskedPrefix,selectedPrefix,programMatrix_nil,Matrix.one_mulVec]
  | succ k ih =>
    rw [maskedPrefix,programMatrix_append,programMatrix_singleton,← Matrix.mulVec_mulVec,ih,
      maskGate_state,selectedPrefix,programMatrix_append,← Matrix.mulVec_mulVec]
    split_ifs <;> simp only [programMatrix_singleton,programMatrix_nil,Matrix.one_mulVec]

def prefixMask (n b : ℕ) : Basis n := fun i => decide (i.val<b)

lemma selectedPrefix_eq (n b k : ℕ) (h : k ≤ n) :
    selectedPrefix (prefixMask n b) k h=hadamardPrefix n (min k b) (by omega) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [selectedPrefix,ih]
    by_cases hk : k<b
    · have hk0 : min k b=k := Nat.min_eq_left (by omega)
      have hk1 : min (k+1) b=k+1 := Nat.min_eq_left (by omega)
      simp only [prefixMask,hk,decide_true,ite_true,hk0,hk1,hadamardPrefix]
    · have hk0 : min k b=b := Nat.min_eq_right (by omega)
      have hk1 : min (k+1) b=b := Nat.min_eq_right (by omega)
      simp only [prefixMask,hk,decide_false,Bool.false_eq_true,ite_false,hk0,hk1,List.append_nil]

/-- Uniformly n gates suffice for EVERY runtime width b<=n. Unlike n fair
bits, the upper n-b bits remain exactly zero, as required for the source list
success bound on small cofactors. -/
lemma maskedPrefix_zero (n b : ℕ) (hb : b ≤ n) :
    (programMatrix (maskedPrefix n n le_rfl)).mulVec
      (basisVector (Fin.append (prefixMask n b) (fun _ => false))) =
      encodeState (fun y => Fin.append (prefixMask n b) y)
        (fun y => if ∀ i : Fin n,b ≤ i.val→y i=false then (Real.sqrt 2:ℂ)⁻¹^b else 0) := by
  rw [← encodeState_basis (fun y => Fin.append (prefixMask n b) y) (fun _ => false),
    maskedPrefix_state,selectedPrefix_eq]
  simp only [Nat.min_eq_right hb,hadamardPrefix_zero]

end ExactQuantumFactoring


end

end OAI
