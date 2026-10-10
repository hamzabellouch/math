import Mathlib
import OAI.Computability.QuantumFactoring.BooleanCircuit

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators

/-- Embed a logical finite state in concrete basis words, including clean work. -/
noncomputable def encodeState {α : Type*} [Fintype α] {q : ℕ}
    (e : α → Basis q) (ψ : α → ℂ) : State q := by
  classical
  exact ∑ a, ψ a • basisVector (e a)

lemma encodeState_apply {α : Type*} [Fintype α] {q : ℕ}
    (e : α → Basis q) (ψ : α → ℂ) (x : Basis q) :
    encodeState e ψ x = ∑ a, if x=e a then ψ a else 0 := by
  classical
  simp only [encodeState, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, basisVector]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> simp

lemma encodeState_at {α : Type*} [Fintype α] {q : ℕ}
    (e : α → Basis q) (he : Function.Injective e) (ψ : α → ℂ) (a : α) :
    encodeState e ψ (e a) = ψ a := by
  classical
  rw [encodeState_apply]
  simp [he.eq_iff]

lemma encodeState_outside {α : Type*} [Fintype α] {q : ℕ}
    (e : α → Basis q) (ψ : α → ℂ) (x : Basis q) (hx : x ∉ Set.range e) :
    encodeState e ψ x = 0 := by
  classical
  rw [encodeState_apply]
  apply Finset.sum_eq_zero
  intro a _
  rw [ite_eq_right]
  intro h
  exact hx ⟨a,h.symm⟩

lemma encodeState_basis {α : Type*} [Fintype α] [DecidableEq α] {q : ℕ}
    (e : α → Basis q) (a : α) : encodeState e (basisVector a) = basisVector (e a) := by
  classical
  simp [encodeState, basisVector, ite_smul]

lemma encodeState_add {α : Type*} [Fintype α] {q : ℕ}
    (e : α → Basis q) (ψ χ : α → ℂ) :
    encodeState e (ψ+χ) = encodeState e ψ + encodeState e χ := by
  classical
  simp only [encodeState, Pi.add_apply, add_smul, Finset.sum_add_distrib]

lemma encodeState_smul {α : Type*} [Fintype α] {q : ℕ}
    (e : α → Basis q) (c : ℂ) (ψ : α → ℂ) :
    encodeState e (c • ψ) = c • encodeState e ψ := by
  classical
  simp only [encodeState, Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

lemma encodeState_sum {α β : Type*} [Fintype α] [Fintype β] {q : ℕ}
    (e : α → Basis q) (ψ : β → α → ℂ) :
    encodeState e (∑ b, ψ b) = ∑ b, encodeState e (ψ b) := by
  classical
  simp only [encodeState, Finset.sum_apply, Finset.sum_smul]
  exact Finset.sum_comm

/-- A basis-level implementation law extends to every coherent superposition. -/
lemma matrix_encodeState {α β : Type*} [Fintype α] [Fintype β] {p q : ℕ}
    (e : α → Basis p) (f : β → Basis q) (U : Matrix (Basis q) (Basis p) ℂ)
    (V : Matrix β α ℂ)
    (h : ∀ a, U.mulVec (basisVector (e a)) = encodeState f (fun b => V b a))
    (ψ : α → ℂ) : U.mulVec (encodeState e ψ) = encodeState f (V.mulVec ψ) := by
  classical
  rw [encodeState, Matrix.mulVec_sum]
  simp only [Matrix.mulVec_smul, h]
  simp_rw [← encodeState_smul]
  rw [← encodeState_sum]
  congr 1
  funext b
  simp only [Finset.sum_apply, Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro a _
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

lemma matrix_encode_permutation {α : Type*} [Fintype α] [DecidableEq α] {q : ℕ}
    (e : α → Basis q) (U : Matrix (Basis q) (Basis q) ℂ) (v : Equiv.Perm α)
    (h : ∀ a, U.mulVec (basisVector (e a)) = basisVector (e (v a)))
    (ψ : α → ℂ) : U.mulVec (encodeState e ψ) = encodeState e (ψ ∘ v.symm) := by
  classical
  rw [encodeState, Matrix.mulVec_sum]
  simp only [Matrix.mulVec_smul, h]
  unfold encodeState
  simpa only [Function.comp_apply, Equiv.symm_apply_apply] using
    Equiv.sum_comp v (fun a => (ψ ∘ v.symm) a • basisVector (e a))

end ExactQuantumFactoring


end

end OAI
