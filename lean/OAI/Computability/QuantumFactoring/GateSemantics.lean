import Mathlib
import OAI.Computability.QuantumFactoring.Basic

namespace OAI

section


namespace ExactQuantumFactoring
open scoped BigOperators

lemma sum_boolFin_succ {α : Type*} [AddCommMonoid α] {n : ℕ}
    (f : (Fin (n+1) → Bool) → α) :
    ∑ x, f x = (∑ x : Fin n → Bool, f (Fin.cons false x)) +
      ∑ x : Fin n → Bool, f (Fin.cons true x) := by
  rw [← (Fin.consEquiv (fun _ : Fin (n+1) => Bool)).sum_comp]
  simpa [Fintype.sum_prod_type, Fin.consEquiv] using
    (add_comm (∑ x : Fin n → Bool, f (Fin.cons true x))
      (∑ x : Fin n → Bool, f (Fin.cons false x)))

lemma sum_boolFin_zero {α : Type*} [AddCommMonoid α]
    (f : (Fin 0 → Bool) → α) : ∑ x, f x = f Fin.elim0 := by
  exact Fintype.sum_unique _

noncomputable def Primitive.localMatrix (p : Primitive) :
    Matrix (Basis p.arity) (Basis p.arity) ℂ :=
  fun x y => p.matrix (List.ofFn x) (List.ofFn y)

/-- A reversible Boolean operation, viewed as an exact permutation matrix. -/
noncomputable def permutationMatrix {ι : Type*} [DecidableEq ι] (e : Equiv.Perm ι) :
    Matrix ι ι ℂ := Matrix.of (fun a b => if a = e b then 1 else 0)

lemma permutationMatrix_unitary {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : Equiv.Perm ι) : permutationMatrix e ∈ Matrix.unitaryGroup ι ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext a b
  simp only [Matrix.mul_apply, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
    permutationMatrix, Matrix.of_apply]
  simp [Finset.sum_ite_eq', e.injective.eq_iff, Matrix.one_apply, eq_comm]

def notPerm : Equiv.Perm (Basis 1) where
  toFun x := ![!x 0]
  invFun x := ![!x 0]
  left_inv x := by ext i; fin_cases i; simp
  right_inv x := by ext i; fin_cases i; simp

def cnotPerm : Equiv.Perm (Basis 2) where
  toFun x := ![x 0, Bool.xor (x 0) (x 1)]
  invFun x := ![x 0, Bool.xor (x 0) (x 1)]
  left_inv x := by ext i; fin_cases i <;> simp
  right_inv x := by ext i; fin_cases i <;> simp

def toffoliPerm : Equiv.Perm (Basis 3) where
  toFun x := ![x 0, x 1, Bool.xor (x 2) (x 0 && x 1)]
  invFun x := ![x 0, x 1, Bool.xor (x 2) (x 0 && x 1)]
  left_inv x := by ext i; fin_cases i <;> simp
  right_inv x := by ext i; fin_cases i <;> simp

lemma not_localMatrix : Primitive.not.localMatrix = permutationMatrix notPerm := by
  change Matrix.of (fun x y : Basis 1 => Primitive.not.matrix (List.ofFn x) (List.ofFn y)) =
    permutationMatrix notPerm
  ext x y
  simp [Primitive.matrix, List.ofFn_succ, Matrix.of_apply,
    permutationMatrix, notPerm, funext_iff, Fin.forall_fin_succ]

lemma cnot_localMatrix : Primitive.cnot.localMatrix = permutationMatrix cnotPerm := by
  change Matrix.of (fun x y : Basis 2 => Primitive.cnot.matrix (List.ofFn x) (List.ofFn y)) =
    permutationMatrix cnotPerm
  ext x y
  simp [Primitive.matrix, List.ofFn_succ, Matrix.of_apply,
    permutationMatrix, cnotPerm, funext_iff, Fin.forall_fin_succ]

lemma toffoli_localMatrix : Primitive.toffoli.localMatrix = permutationMatrix toffoliPerm := by
  change Matrix.of (fun x y : Basis 3 => Primitive.toffoli.matrix (List.ofFn x) (List.ofFn y)) =
    permutationMatrix toffoliPerm
  ext x y
  simp [Primitive.matrix, List.ofFn_succ, Matrix.of_apply,
    permutationMatrix, toffoliPerm, funext_iff, Fin.forall_fin_succ]

lemma hadamard_local_unitary : Primitive.hadamard.localMatrix ∈
    Matrix.unitaryGroup (Basis Primitive.hadamard.arity) ℂ := by
  change Matrix.of (fun x y : Fin 1 → Bool =>
    Primitive.hadamard.matrix (List.ofFn x) (List.ofFn y)) ∈
    Matrix.unitaryGroup (Fin 1 → Bool) ℂ
  rw [Matrix.mem_unitaryGroup_iff']
  ext x y
  simp only [Matrix.mul_apply, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, Matrix.of_apply]
  rw [sum_boolFin_succ]
  simp only [sum_boolFin_zero]
  have hx : x = Fin.cons (x 0) Fin.elim0 := by ext i; fin_cases i; rfl
  have hy : y = Fin.cons (y 0) Fin.elim0 := by ext i; fin_cases i; rfl
  rw [hx, hy]
  have hs : (Real.sqrt 2 : ℂ)^2 = 2 := by
    norm_cast
    exact Real.sq_sqrt (by norm_num)
  cases x 0 <;> cases y 0 <;>
    simp [Primitive.matrix, List.ofFn_succ] <;> ring_nf <;>
      simp [inv_pow, hs]

lemma phase_local_unitary : Primitive.phase.localMatrix ∈
    Matrix.unitaryGroup (Basis Primitive.phase.arity) ℂ := by
  change Matrix.of (fun x y : Fin 1 → Bool =>
    Primitive.phase.matrix (List.ofFn x) (List.ofFn y)) ∈
    Matrix.unitaryGroup (Fin 1 → Bool) ℂ
  rw [Matrix.mem_unitaryGroup_iff']
  ext x y
  simp only [Matrix.mul_apply, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, Matrix.of_apply]
  rw [sum_boolFin_succ]
  simp only [sum_boolFin_zero]
  have hx : x = Fin.cons (x 0) Fin.elim0 := by ext i; fin_cases i; rfl
  have hy : y = Fin.cons (y 0) Fin.elim0 := by ext i; fin_cases i; rfl
  rw [hx, hy]
  cases x 0 <;> cases y 0 <;> simp [Primitive.matrix, List.ofFn_succ]

lemma Primitive.local_unitary (p : Primitive) :
    p.localMatrix ∈ Matrix.unitaryGroup (Basis p.arity) ℂ := by
  cases p with
  | not => rw [not_localMatrix]; exact permutationMatrix_unitary _
  | cnot => rw [cnot_localMatrix]; exact permutationMatrix_unitary _
  | toffoli => rw [toffoli_localMatrix]; exact permutationMatrix_unitary _
  | hadamard => exact hadamard_local_unitary
  | phase => exact phase_local_unitary

lemma unitary_reindex {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (e : ι ≃ κ) (A : Matrix ι ι ℂ)
    (hA : A ∈ Matrix.unitaryGroup ι ℂ) :
    Matrix.reindex e e A ∈ Matrix.unitaryGroup κ ℂ := by
  rw [Matrix.mem_unitaryGroup_iff'] at hA ⊢
  have hs : star (Matrix.reindex e e A) = Matrix.reindex e e (star A) :=
    Matrix.conjTranspose_reindex e e A
  rw [hs]
  change Matrix.reindexAlgEquiv ℂ ℂ e (star A) * Matrix.reindexAlgEquiv ℂ ℂ e A = 1
  rw [← map_mul, hA, map_one]

noncomputable def controlledMatrix {ι : Type*} [DecidableEq ι] (A : Matrix ι ι ℂ) :
    Matrix (Bool × ι) (Bool × ι) ℂ :=
  Matrix.of (fun x y => if x.1 = y.1 then
    if x.1 then A x.2 y.2 else if x.2 = y.2 then 1 else 0
    else 0)

lemma controlledMatrix_unitary {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (hA : A ∈ Matrix.unitaryGroup ι ℂ) :
    controlledMatrix A ∈ Matrix.unitaryGroup (Bool × ι) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff'] at hA ⊢
  ext ⟨a,x⟩ ⟨b,y⟩
  simp only [Matrix.mul_apply, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply]
  rw [Fintype.sum_prod_type, Fintype.sum_bool]
  cases a <;> cases b <;>
    simp [controlledMatrix, Matrix.one_apply]
  · by_cases h : x = y
    · subst y; simp
    · simp [h, Ne.symm h]
  · simpa [Matrix.mul_apply, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
      Matrix.one_apply] using congrFun (congrFun hA x) y

noncomputable def Gate.baseLocalMatrix (g : Gate) :
    Matrix (Basis g.primitive.arity) (Basis g.primitive.arity) ℂ :=
  Matrix.of (fun x y => g.baseMatrix (List.ofFn x) (List.ofFn y))

lemma Gate.baseLocalMatrix_eq (g : Gate) : g.baseLocalMatrix =
    if g.inverse then star g.primitive.localMatrix else g.primitive.localMatrix := by
  ext x y
  cases hi : g.inverse <;>
    simp [Gate.baseLocalMatrix, Gate.baseMatrix, Primitive.localMatrix, hi]

lemma Gate.baseLocal_unitary (g : Gate) :
    g.baseLocalMatrix ∈ Matrix.unitaryGroup (Basis g.primitive.arity) ℂ := by
  rw [g.baseLocalMatrix_eq]
  split_ifs
  · exact Unitary.star_mem g.primitive.local_unitary
  · exact g.primitive.local_unitary

noncomputable def Gate.localMatrix (g : Gate) : Matrix (Basis g.arity) (Basis g.arity) ℂ :=
  Matrix.of (fun x y => g.matrix (List.ofFn x) (List.ofFn y))

lemma Gate.controlled_localMatrix (p : Primitive) (inv : Bool) :
    (Gate.mk p inv true).localMatrix =
    Matrix.reindex (Fin.consEquiv (fun _ : Fin (p.arity+1) => Bool))
      (Fin.consEquiv (fun _ : Fin (p.arity+1) => Bool))
      (controlledMatrix (Gate.mk p inv true).baseLocalMatrix) := by
  change Matrix.of (fun x y : Basis (p.arity+1) =>
    (Gate.mk p inv true).matrix (List.ofFn x) (List.ofFn y)) = _
  ext x y
  simp only [Gate.matrix, ↓reduceIte, List.ofFn_succ, Matrix.of_apply,
    Matrix.reindex_apply, Fin.consEquiv, controlledMatrix,
    Gate.baseLocalMatrix]
  cases hx : x 0 <;> cases hy : y 0 <;> simp [hx, hy, Fin.tail_def]

lemma Gate.local_unitary (g : Gate) : g.localMatrix ∈ Matrix.unitaryGroup (Basis g.arity) ℂ := by
  rcases g with ⟨p, inv, ctrl⟩
  cases ctrl
  · exact Gate.baseLocal_unitary ⟨p, inv, false⟩
  · rw [Gate.controlled_localMatrix]
    exact unitary_reindex _ _ (controlledMatrix_unitary _ (Gate.baseLocal_unitary _))

end ExactQuantumFactoring


end

end OAI
