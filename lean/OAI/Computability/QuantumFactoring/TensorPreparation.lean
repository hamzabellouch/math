import Mathlib
import OAI.Computability.QuantumFactoring.RepeatedTrials
import OAI.Computability.QuantumFactoring.TrialRawPreparation

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open Exactness RepeatedTrials

abbrev tensorWidth (q : ℕ) : ℕ→ℕ
  | 0 => 0
  | K+1 => q+tensorWidth q K

lemma tensorWidth_eq (q K : ℕ) : tensorWidth q K=K*q := by
  induction K with
  | zero => simp [tensorWidth]
  | succ K ih => simp [tensorWidth,ih,Nat.add_mul,Nat.add_comm]

def tensorLayout (q : ℕ) : (K : ℕ)→(Fin K→Basis q)≃Basis (tensorWidth q K)
  | 0 => Equiv.ofUnique _ _
  | K+1 => (Fin.consEquiv (fun _ : Fin (K+1) => Basis q)).symm.trans
      (productLayout (Equiv.refl _) (tensorLayout q K))

lemma tensorLayout_succ (q K : ℕ) (x : Fin (K+1)→Basis q) :
    tensorLayout q (K+1) x=Fin.append (x 0) (tensorLayout q K (Fin.tail x)) := rfl

def tensorProgram {q : ℕ} (ops : List (Instruction q)) : (K : ℕ)→List (Instruction (tensorWidth q K))
  | 0 => []
  | K+1 => parallelProgram ops (tensorProgram ops K)

lemma tensorProgram_length {q : ℕ} (ops : List (Instruction q)) (K : ℕ) :
    (tensorProgram ops K).length=K*ops.length := by
  induction K with
  | zero => simp [tensorProgram]
  | succ K ih => rw [tensorProgram,parallelProgram_length,ih]; ring

lemma tensorProgram_entry {q : ℕ} (ops : List (Instruction q)) (K : ℕ)
    (x y : Fin K→Basis q) :
    (programMatrix (tensorProgram ops K)).mulVec (basisVector (tensorLayout q K x)) (tensorLayout q K y)=
      ∏ i, (programMatrix ops).mulVec (basisVector (x i)) (y i) := by
  induction K with
  | zero =>
    have he : x=y := Subsingleton.elim _ _
    subst y
    simp [tensorProgram,programMatrix,basisVector]
  | succ K ih =>
    rw [tensorProgram,tensorLayout_succ,tensorLayout_succ,parallelProgram_entry,ih,Fin.prod_univ_succ]
    rfl

/-- A literal repeated finite-gate program, not just a tensor-state idealization. -/
lemma tensorProgram_state {q : ℕ} (ops : List (Instruction q)) (K : ℕ) (x : Basis q) :
    (programMatrix (tensorProgram ops K)).mulVec (basisVector (tensorLayout q K (fun _ => x)))=
      encodeState (tensorLayout q K) (tensorState ((programMatrix ops).mulVec (basisVector x)) K) := by
  funext y
  obtain ⟨z,rfl⟩ := (tensorLayout q K).surjective y
  rw [tensorProgram_entry,encodeState_at _ (tensorLayout q K).injective]
  rfl

lemma tensorProgram_event {q : ℕ} (ops : List (Instruction q)) (K : ℕ) (x : Basis q)
    (P : (Fin K→Basis q)→Prop) :
    outcomeMass (P ∘ (tensorLayout q K).symm)
      ((programMatrix (tensorProgram ops K)).mulVec (basisVector (tensorLayout q K (fun _ => x))))=
      outcomeMass P (tensorState ((programMatrix ops).mulVec (basisVector x)) K) := by
  rw [tensorProgram_state,outcomeMass_encode _ (tensorLayout q K).injective]
  congr 1
  funext y
  simp

end ExactQuantumFactoring


end

end OAI
