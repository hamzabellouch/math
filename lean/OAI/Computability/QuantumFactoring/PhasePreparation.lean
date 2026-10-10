import Mathlib
import OAI.Computability.QuantumFactoring.SuperpositionGates

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators

lemma hadamardAt_apply {q : ℕ} (t : Fin q) (ψ : State q) (y : Basis q) :
    (hadamardAt t).matrix.mulVec ψ y =
      (ψ (Function.update y t false) +
        (if y t then (-1 : ℂ) else 1) * ψ (Function.update y t true)) / (Real.sqrt 2 : ℂ) := by
  classical
  change (∑ x, (hadamardAt t).matrix y x * ψ x) = _
  have hne : Function.update y t false ≠ Function.update y t true := by
    intro h; have := congrFun h t; simp at this
  rw [Finset.sum_eq_add (Function.update y t false) (Function.update y t true) hne]
  · rw [hadamardAt_matrix, hadamardAt_matrix]
    have h₀ : ∀ i, i ≠ t → y i = Function.update y t false i := by
      intro i hi; simp [Function.update_of_ne hi]
    have h₁ : ∀ i, i ≠ t → y i = Function.update y t true i := by
      intro i hi; simp [Function.update_of_ne hi]
    rw [ite_eq_left h₀, ite_eq_left h₁]
    simp only [Function.update_self, Bool.and_false, Bool.false_eq_true, ite_false, Bool.and_true]
    ring
  · intro x _ hx
    rw [hadamardAt_matrix]
    suffices ¬ ∀ i, i ≠ t → y i = x i by rw [ite_eq_right this, zero_mul]
    intro ho
    have he : x = Function.update y t (x t) := by
      apply (eq_update_iff ..).2
      exact ⟨rfl, fun i hi => (ho i hi).symm⟩
    cases ht : x t
    · exact hx.1 (ht ▸ he)
    · exact hx.2 (ht ▸ he)
  · simp
  · simp

lemma phaseAt_apply {q : ℕ} (t : Fin q) (ψ : State q) (y : Basis q) :
    (phaseAt t).matrix.mulVec ψ y = (if y t then Complex.I else 1) * ψ y := by
  classical
  change (∑ x, (phaseAt t).matrix y x * ψ x) = _
  rw [Finset.sum_eq_single y]
  · simp [phaseAt_matrix]
  · intro x _ h; simp [phaseAt_matrix, Ne.symm h]
  · simp

/-- Hadamards on increasing physical wires; no multi-qubit gate abbreviation. -/
def hadamardPrefix (q : ℕ) : (k : ℕ) → k ≤ q → List (Instruction q)
  | 0, _ => []
  | k+1, h => hadamardPrefix q k (by omega) ++ [hadamardAt ⟨k, by omega⟩]

lemma hadamardPrefix_length (q k : ℕ) (h : k ≤ q) : (hadamardPrefix q k h).length = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [hadamardPrefix, ih]

lemma hadamardPrefix_zero (q k : ℕ) (h : k ≤ q) :
    (programMatrix (hadamardPrefix q k h)).mulVec (basisVector (fun _ => false)) =
      (fun y => if ∀ i : Fin q, k ≤ i.val → y i = false then (Real.sqrt 2 : ℂ)⁻¹ ^ k else 0) := by
  classical
  induction k with
  | zero =>
    rw [hadamardPrefix, programMatrix_nil, Matrix.one_mulVec]
    funext y
    simp only [basisVector, pow_zero, Nat.zero_le, forall_const]
    have : y = (fun _ => false) ↔ ∀ i, y i = false := by
      constructor
      · rintro rfl; simp
      · exact funext
    simp only [this]
  | succ k ih =>
    rw [hadamardPrefix, programMatrix_append, programMatrix_singleton,
      ← Matrix.mulVec_mulVec, ih (by omega)]
    funext y
    rw [hadamardAt_apply]
    have hfalse : (∀ i : Fin q, k ≤ i.val → Function.update y ⟨k, by omega⟩ false i = false) ↔
        (∀ i : Fin q, k+1 ≤ i.val → y i = false) := by
      constructor
      · intro hh i hi
        have hn : i ≠ (⟨k, by omega⟩ : Fin q) := by intro he; have hh := congrArg Fin.val he; change i.val = k at hh; omega
        simpa [Function.update_of_ne hn] using hh i (by omega)
      · intro hh i hi
        by_cases he : i.val = k
        · have he' : i = (⟨k, by omega⟩ : Fin q) := Fin.ext he
          simp [he']
        · rw [Function.update_of_ne (by intro he'; exact he (congrArg Fin.val he'))]
          exact hh i (by omega)
    have htrue : ¬ ∀ i : Fin q, k ≤ i.val → Function.update y ⟨k, by omega⟩ true i = false := by
      intro hh
      have := hh ⟨k, by omega⟩ le_rfl
      simp at this
    simp only [hfalse, ite_eq_right htrue, mul_zero, add_zero]
    split_ifs <;> simp [pow_succ, div_eq_mul_inv]

lemma hadamards_zero (q : ℕ) :
    (programMatrix (hadamardPrefix q q le_rfl)).mulVec (basisVector (fun _ => false)) =
      fun _ => (Real.sqrt 2 : ℂ)⁻¹ ^ q := by
  rw [hadamardPrefix_zero]
  funext y
  rw [ite_eq_left (by intro i hi; exact False.elim (Nat.not_le.mpr i.isLt hi))]

/-- The exact phase-state preparation from Section 3.1: H on every wire,
Z=S² on the most significant wire, and S on the next wire. -/
def preparePhase (b : ℕ) (hb : 2 ≤ b) : List (Instruction b) :=
  hadamardPrefix b b le_rfl ++
    [phaseAt ⟨b-1, by omega⟩, phaseAt ⟨b-1, by omega⟩, phaseAt ⟨b-2, by omega⟩]

lemma preparePhase_length (b : ℕ) (hb : 2 ≤ b) : (preparePhase b hb).length = b+3 := by
  simp [preparePhase, hadamardPrefix_length]

lemma preparePhase_correct (b : ℕ) (hb : 2 ≤ b) (y : Basis b) :
    (programMatrix (preparePhase b hb)).mulVec (basisVector (fun _ => false)) y =
      (Real.sqrt 2 : ℂ)⁻¹ ^ b *
        (if y ⟨b-1, by omega⟩ then (-1 : ℂ) else 1) *
        (if y ⟨b-2, by omega⟩ then Complex.I else 1) := by
  rw [preparePhase, programMatrix_append, ← Matrix.mulVec_mulVec, hadamards_zero]
  rw [programMatrix_cons, programMatrix_cons, programMatrix_singleton,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rw [phaseAt_apply, phaseAt_apply, phaseAt_apply]
  cases y ⟨b-1, by omega⟩ <;> cases y ⟨b-2, by omega⟩ <;> simp <;> ring_nf <;> simp [Complex.I_sq]

end ExactQuantumFactoring


end

end OAI
