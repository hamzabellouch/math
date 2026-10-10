import Mathlib
import OAI.Computability.QuantumFactoring.PackedEncoding

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open BooleanNetwork

lemma packed_eq_iff {n m r : ℕ} (x z : Basis n) (y u : Basis m) :
    packed r x y = packed r z u ↔ x=z ∧ y=u := by
  constructor
  · intro h
    have hh := BooleanNetwork.packed_injective (n := n) (m := m) (r := r)
      (a₁ := (x,y)) (a₂ := (z,u)) h
    exact ⟨congrArg Prod.fst hh,congrArg Prod.snd hh⟩
  · rintro ⟨rfl,rfl⟩
    rfl

lemma encoded_packed_coordinate {n m r : ℕ} (y u : Basis m) (ψ : State n)
    (z : Basis n) :
    encodeState (fun x => packed r x y) ψ (packed r z u) = if u=y then ψ z else 0 := by
  classical
  rw [encodeState_apply]
  simp only [packed_eq_iff]
  by_cases hu : u=y
  · simp [hu]
  · simp [hu]

/-- Retain the modular value register while interfering the exponent register;
no copy of the exponent or hidden measurement is inserted. -/
def sampleProgram {n m r : ℕ} (c : BooleanNetwork n m) (hr : c.net.count ≤ r)
    (ops : List (Instruction n)) : List (Instruction (n+m+r)) :=
  oracleOn c hr ++ firstProgram m r ops

lemma sampleProgram_length {n m r : ℕ} (c : BooleanNetwork n m) (hr : c.net.count ≤ r)
    (ops : List (Instruction n)) :
    (sampleProgram c hr ops).length ≤ 4*c.net.count+2*m+ops.length := by
  have h := oracleOn_length c hr
  simp only [sampleProgram,List.length_append,firstProgram_length]
  omega

lemma sampleProgram_amplitude {n m r : ℕ} (c : BooleanNetwork n m)
    (hr : c.net.count ≤ r) (ops : List (Instruction n)) (ψ : State n)
    (z : Basis n) (u : Basis m) :
    (programMatrix (sampleProgram c hr ops)).mulVec
      (encodeState (fun x => packed r x (fun _ => false)) ψ) (packed r z u) =
      ∑ x, if c.eval x=u then programMatrix ops z x * ψ x else 0 := by
  classical
  rw [sampleProgram,programMatrix_append,← Matrix.mulVec_mulVec,oracleOn_state]
  rw [encodeState,Matrix.mulVec_sum]
  simp_rw [Matrix.mulVec_smul,firstProgram_basis]
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,encoded_packed_coordinate,
    matrix_basisVector]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : c.eval x=u
  · simp only [h,ite_true]
    ring
  · simp only [h,ite_false,show u ≠ c.eval x from Ne.symm h,mul_zero]

/-- Coherent sampling on an explicitly encoded logical subspace. Inactive
quantum registers stay present; normalization need not be inferred by analogy
with a stochastic oracle. -/
lemma sampleProgram_encoded_amplitude {α : Type*} [Fintype α]
    {n m r : ℕ} (e : α → Basis n) (c : BooleanNetwork n m)
    (hr : c.net.count ≤ r) (ops : List (Instruction n)) (ψ : α → ℂ)
    (z : Basis n) (u : Basis m) :
    (programMatrix (sampleProgram c hr ops)).mulVec
      (encodeState (fun x => packed r (e x) (fun _ => false)) ψ) (packed r z u) =
      ∑ x, if c.eval (e x)=u then programMatrix ops z (e x) * ψ x else 0 := by
  classical
  rw [sampleProgram,programMatrix_append,← Matrix.mulVec_mulVec]
  rw [encodeState,Matrix.mulVec_sum]
  simp only [Matrix.mulVec_smul,oracleOn_basis,Bool.false_xor]
  rw [Matrix.mulVec_sum]
  simp_rw [Matrix.mulVec_smul,firstProgram_basis]
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,encoded_packed_coordinate,
    matrix_basisVector]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : c.eval (e x)=u
  · simp only [h,ite_true]
    ring
  · simp only [h,ite_false,show u ≠ c.eval (e x) from Ne.symm h,mul_zero]

end ExactQuantumFactoring


end

end OAI
