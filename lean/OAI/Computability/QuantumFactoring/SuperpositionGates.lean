import Mathlib
import OAI.Computability.QuantumFactoring.BooleanProgram

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators

abbrev phaseAt {q : ℕ} (t : Fin q) : Instruction q :=
  ⟨plainGate .phase, fun _ => t, by
    change Function.Injective (fun _ : Fin 1 => t)
    intro a b _; exact Subsingleton.elim a b⟩

abbrev hadamardAt {q : ℕ} (t : Fin q) : Instruction q :=
  ⟨plainGate .hadamard, fun _ => t, by
    change Function.Injective (fun _ : Fin 1 => t)
    intro a b _; exact Subsingleton.elim a b⟩

lemma eq_update_iff {q : ℕ} (x y : Basis q) (t : Fin q) (b : Bool) :
    y = Function.update x t b ↔ y t = b ∧ ∀ i, i ≠ t → y i = x i := by
  classical
  constructor
  · rintro rfl
    exact ⟨Function.update_self _ _ _, fun i hi => Function.update_of_ne hi _ _⟩
  · rintro ⟨ht,ho⟩
    funext i
    by_cases hi : i = t
    · subst i; simpa using ht
    · simpa [Function.update_of_ne hi] using ho i hi

lemma phaseAt_matrix {q : ℕ} (t : Fin q) (x y : Basis q) :
    (phaseAt t).matrix y x = if y = x then (if x t then Complex.I else 1) else 0 := by
  classical
  change (if ∀ i : Fin q, (∀ _ : Fin 1, t ≠ i) → y i = x i then
      (plainGate .phase).matrix (List.ofFn (fun _ : Fin 1 => y t))
        (List.ofFn (fun _ : Fin 1 => x t)) else 0) = _
  simp only [Gate.matrix, Gate.baseMatrix, Bool.false_eq_true, ite_false, List.ofFn_succ,
    List.ofFn_zero, Primitive.matrix]
  by_cases he : y = x
  · subst y; simp
  · by_cases ht : y t = x t
    · have ho : ¬ ∀ i : Fin q, t ≠ i → y i = x i := by
        intro hh
        apply he
        funext i
        by_cases hi : t = i
        · subst i; exact ht
        · exact hh i hi
      simp [he, ho]
    · simp [he, ht]

lemma phaseAt_basis {q : ℕ} (t : Fin q) (x : Basis q) :
    (phaseAt t).matrix.mulVec (basisVector x) =
      (if x t then Complex.I else 1) • basisVector x := by
  classical
  rw [matrix_basisVector]
  funext y
  rw [phaseAt_matrix]
  by_cases he : y = x <;> simp [basisVector, he]

lemma phaseSquared_basis {q : ℕ} (t : Fin q) (x : Basis q) :
    (programMatrix [phaseAt t, phaseAt t]).mulVec (basisVector x) =
      (if x t then (-1 : ℂ) else 1) • basisVector x := by
  rw [programMatrix_cons, programMatrix_singleton, ← Matrix.mulVec_mulVec,
    phaseAt_basis, Matrix.mulVec_smul, phaseAt_basis, smul_smul]
  cases x t <;> simp

lemma BooleanProgram.phase_compute_uncompute {q : ℕ} (p : BooleanProgram q)
    (t : Fin q) (x : Basis q) :
    (programMatrix (p.compile ++ [phaseAt t, phaseAt t] ++
      p.compile.reverse.map Instruction.reverse)).mulVec (basisVector x) =
      (if p.eval x t then (-1 : ℂ) else 1) • basisVector x := by
  rw [programMatrix_append, programMatrix_append, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, p.compile_basis x, phaseSquared_basis,
    Matrix.mulVec_smul, p.uncompute x]

lemma hadamardAt_matrix {q : ℕ} (t : Fin q) (x y : Basis q) :
    (hadamardAt t).matrix y x =
      if ∀ i, i ≠ t → y i = x i then
        (if y t && x t then (-1 : ℂ) else 1) / (Real.sqrt 2 : ℂ) else 0 := by
  classical
  change (if ∀ i : Fin q, (∀ _ : Fin 1, t ≠ i) → y i = x i then
      (plainGate .hadamard).matrix (List.ofFn (fun _ : Fin 1 => y t))
        (List.ofFn (fun _ : Fin 1 => x t)) else 0) = _
  simp only [Gate.matrix, Gate.baseMatrix, Bool.false_eq_true, ite_false, List.ofFn_succ,
    List.ofFn_zero, Primitive.matrix]
  have he : (∀ i, t ≠ i → y i = x i) ↔ (∀ i, i ≠ t → y i = x i) := by
    constructor <;> intro h i hi <;> exact h i (Ne.symm hi)
  simp only [forall_const, he]

lemma hadamardAt_basis {q : ℕ} (t : Fin q) (x : Basis q) :
    (hadamardAt t).matrix.mulVec (basisVector x) =
      (Real.sqrt 2 : ℂ)⁻¹ • (basisVector (Function.update x t false) +
        (if x t then (-1 : ℂ) else 1) • basisVector (Function.update x t true)) := by
  classical
  rw [matrix_basisVector]
  funext y
  rw [hadamardAt_matrix]
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, basisVector, eq_update_iff]
  by_cases ho : ∀ i, i ≠ t → y i = x i
  · cases hx : x t <;> cases hy : y t <;> simp_all [div_eq_mul_inv]
  · simp [ho]

end ExactQuantumFactoring


end

end OAI
