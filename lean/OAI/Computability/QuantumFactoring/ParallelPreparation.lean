import Mathlib
import OAI.Computability.QuantumFactoring.AppendRegister
import OAI.Computability.QuantumFactoring.FactorGuess
import OAI.Computability.QuantumFactoring.RecordedHistory

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open BooleanNetwork Exactness

def leftRegister (p q : ℕ) : Register p (p+q) := ⟨Fin.castAdd q,Fin.castAdd_injective p q⟩
lemma append_leftRegister {p q : ℕ} (x : Basis p) (y : Basis q) :
    Fin.append x y ∘ leftRegister p q=x := by
  funext i
  exact Fin.append_left _ _ i
lemma append_replace_left {p q : ℕ} (x z : Basis p) (y : Basis q) :
    (leftRegister p q).replace (Fin.append x y) z=Fin.append z y := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · change (leftRegister p q).replace (Fin.append x y) z (leftRegister p q j)=_
    rw [Register.replace_inside,Fin.append_left]
  · have hj : ∀ k, leftRegister p q k≠Fin.natAdd p j := by
      intro k h
      have hh := congrArg Fin.val h
      change k.val=p+j.val at hh
      have := k.isLt
      omega
    rw [Register.replace_outside _ _ _ ⟨Fin.natAdd p j,hj⟩]
    simp only [Fin.append_right]

def leftProgram {p : ℕ} (q : ℕ) (ops : List (Instruction p)) : List (Instruction (p+q)) :=
  ops.map (Instruction.place (leftRegister p q))
lemma leftProgram_basis {p q : ℕ} (ops : List (Instruction p)) (x : Basis p) (y : Basis q) :
    (programMatrix (leftProgram q ops)).mulVec (basisVector (Fin.append x y))=
      encodeState (fun z => Fin.append z y) ((programMatrix ops).mulVec (basisVector x)) := by
  rw [leftProgram,Register.placed_basis_state,append_leftRegister]
  congr 1
  funext z
  exact append_replace_left x z y

def appendEquiv (p q : ℕ) : Basis p × Basis q ≃ Basis (p+q) :=
  Fin.appendEquiv p q
lemma appendEquiv_apply {p q : ℕ} (xy : Basis p × Basis q) :
    appendEquiv p q xy=Fin.append xy.1 xy.2 := rfl

noncomputable def independentState {α β : Type*} (ψ : α→ℂ) (χ : β→ℂ) : α×β→ℂ :=
  fun xy => ψ xy.1*χ xy.2

lemma encode_independent {α β : Type*} [Fintype α] [Fintype β] {p q : ℕ}
    (e : α→Basis p) (f : β→Basis q) (ψ : α→ℂ) (χ : β→ℂ) :
    encodeState (fun xy : α×β => Fin.append (e xy.1) (f xy.2)) (independentState ψ χ)=
      ∑ x, ψ x • encodeState (fun y => Fin.append (e x) (f y)) χ := by
  unfold encodeState independentState
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro y _
  rw [smul_smul]

def parallelProgram {p q : ℕ} (A : List (Instruction p)) (B : List (Instruction q)) :
    List (Instruction (p+q)) := leftProgram q A ++ rightProgram p B
lemma parallelProgram_length {p q : ℕ} (A : List (Instruction p)) (B : List (Instruction q)) :
    (parallelProgram A B).length=A.length+B.length := by
  simp [parallelProgram,leftProgram,rightProgram]

lemma parallelProgram_basis {p q : ℕ} (A : List (Instruction p)) (B : List (Instruction q))
    (x : Basis p) (y : Basis q) :
    (programMatrix (parallelProgram A B)).mulVec (basisVector (Fin.append x y))=
      encodeState (appendEquiv p q) (independentState
        ((programMatrix A).mulVec (basisVector x)) ((programMatrix B).mulVec (basisVector y))) := by
  rw [parallelProgram,programMatrix_append,← Matrix.mulVec_mulVec,leftProgram_basis]
  rw [encodeState,Matrix.mulVec_sum]
  simp only [Matrix.mulVec_smul,rightProgram_basis]
  exact (encode_independent id id _ _).symm

lemma independent_mass {α β : Type*} [Fintype α] [Fintype β]
    (ψ : α→ℂ) (χ : β→ℂ) (P : α→Prop) (R : β→Prop) :
    outcomeMass (fun xy : α×β => P xy.1 ∧ R xy.2) (independentState ψ χ)=
      outcomeMass P ψ*outcomeMass R χ := by
  exact RecordedHistory.append_constant_mass ψ (fun _ => χ) P (fun _ => R) _ (fun _ _ => rfl)

lemma independent_mass_left {α β : Type*} [Fintype α] [Fintype β]
    (ψ : α→ℂ) (χ : β→ℂ) (P : α→Prop) (hχ : ∑ y, Complex.normSq (χ y)=1) :
    outcomeMass (fun xy : α×β => P xy.1) (independentState ψ χ)=outcomeMass P ψ := by
  have hh := independent_mass ψ χ P (fun _ => True)
  have he : (fun xy : α×β => P xy.1 ∧ True)=(fun xy => P xy.1) := by funext xy; simp
  have hn : outcomeMass (fun _ : β => True) χ=1 := by
    unfold outcomeMass
    simpa only [ite_true] using hχ
  rw [he,hn,mul_one] at hh
  exact hh

lemma independent_mass_right {α β : Type*} [Fintype α] [Fintype β]
    (ψ : α→ℂ) (χ : β→ℂ) (R : β→Prop) (hψ : ∑ x, Complex.normSq (ψ x)=1) :
    outcomeMass (fun xy : α×β => R xy.2) (independentState ψ χ)=outcomeMass R χ := by
  have hh := independent_mass ψ χ (fun _ => True) R
  have he : (fun xy : α×β => True ∧ R xy.2)=(fun xy => R xy.2) := by funext xy; simp
  have hn : outcomeMass (fun _ : α => True) ψ=1 := by
    unfold outcomeMass
    simpa only [ite_true] using hψ
  rw [he,hn,one_mul] at hh
  exact hh

lemma fair_normalized (b : ℕ) : ∑ x : Basis b, Complex.normSq (fairState b x)=1 := by
  exact fairState_normalized b

lemma basis_preparation_normalized {q : ℕ} (A : List (Instruction q)) (x : Basis q) :
    ∑ y, Complex.normSq ((programMatrix A).mulVec (basisVector x) y)=1 := by
  rw [unitary_mass _ (programMatrix_unitary _)]
  simp [basisVector]

end ExactQuantumFactoring


end

end OAI
