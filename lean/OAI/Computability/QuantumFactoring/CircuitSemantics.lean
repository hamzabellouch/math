import Mathlib
import OAI.Computability.QuantumFactoring.ExactnessFurther
import OAI.Computability.QuantumFactoring.GateSemantics

namespace OAI

section


namespace ExactQuantumFactoring
open scoped BigOperators Kronecker

abbrev Instruction.Unused {q : ℕ} (o : Instruction q) :=
  {i : Fin q // ∀ j, o.wire j ≠ i}

/-- Reindex a full computational basis by the gate wires and all other wires.
This is only a proof equivalence; it introduces no new gate in the model. -/
noncomputable def Instruction.splitBasis {q : ℕ} (o : Instruction q) :
    Basis q ≃ Basis o.gate.arity × (o.Unused → Bool) := by
  classical
  refine {
    toFun := fun x => (x ∘ o.wire, fun i => x i.val)
    invFun := fun x i => if h : ∃ j, o.wire j = i then x.1 h.choose
      else x.2 ⟨i, by simpa only [not_exists] using h⟩
    left_inv := ?_
    right_inv := ?_ }
  · intro x
    funext i
    dsimp
    split_ifs with h
    · simp only [h.choose_spec]
    · rfl
  · intro x
    apply Prod.ext
    · funext j
      dsimp
      have h : ∃ j', o.wire j' = o.wire j := ⟨j, rfl⟩
      rw [dite_eq_left h]
      exact congrArg x.1 (o.distinct h.choose_spec)
    · funext i
      dsimp
      rw [dite_eq_right (by simpa only [not_exists] using i.property)]

lemma tensor_unitary {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (A : Matrix ι ι ℂ) (B : Matrix κ κ ℂ)
    (hA : A ∈ Matrix.unitaryGroup ι ℂ) (hB : B ∈ Matrix.unitaryGroup κ ℂ) :
    A ⊗ₖ B ∈ Matrix.unitaryGroup (ι × κ) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff'] at hA hB ⊢
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker]
  rw [← Matrix.mul_kronecker_mul]
  change (star A * A) ⊗ₖ (star B * B) = 1
  rw [hA, hB, Matrix.one_kronecker_one]

lemma Instruction.matrix_eq_reindex {q : ℕ} (o : Instruction q) :
    o.matrix = Matrix.reindex o.splitBasis.symm o.splitBasis.symm
      (o.gate.localMatrix ⊗ₖ (1 : Matrix (o.Unused → Bool) (o.Unused → Bool) ℂ)) := by
  classical
  ext x y
  change (if ∀ i : Fin q, (∀ j, o.wire j ≠ i) → x i = y i then
      o.gate.matrix (List.ofFn (x ∘ o.wire)) (List.ofFn (y ∘ o.wire)) else 0) =
    o.gate.matrix (List.ofFn (x ∘ o.wire)) (List.ofFn (y ∘ o.wire)) *
      if (fun i : o.Unused => x i.val) = (fun i : o.Unused => y i.val) then 1 else 0
  by_cases h : ∀ i : Fin q, (∀ j, o.wire j ≠ i) → x i = y i
  · have he : (fun i : o.Unused => x i.val) = (fun i : o.Unused => y i.val) :=
      funext (fun i => h i.val i.property)
    rw [ite_eq_left h, ite_eq_left he, mul_one]
  · have he : (fun i : o.Unused => x i.val) ≠ (fun i : o.Unused => y i.val) := by
      intro hh
      apply h
      intro i hi
      exact congrFun hh ⟨i,hi⟩
    rw [ite_eq_right h, ite_eq_right he, mul_zero]

lemma Instruction.unitary {q : ℕ} (o : Instruction q) :
    o.matrix ∈ Matrix.unitaryGroup (Basis q) ℂ := by
  classical
  rw [o.matrix_eq_reindex]
  exact unitary_reindex _ _ (tensor_unitary _ _ o.gate.local_unitary (one_mem _))

/-- Matrix of executing a list of instructions, in chronological order. -/
noncomputable def programMatrix {q : ℕ} (ops : List (Instruction q)) :
    Matrix (Basis q) (Basis q) ℂ :=
  ops.foldl (fun A (o : Instruction _) => o.matrix * A) 1

lemma programMatrix_fold {q : ℕ} (ops : List (Instruction q))
    (A : Matrix (Basis q) (Basis q) ℂ) :
    ops.foldl (fun A (o : Instruction _) => o.matrix * A) A = programMatrix ops * A := by
  induction ops generalizing A with
  | nil => simp [programMatrix]
  | cons o ops ih =>
    change ops.foldl (fun A (o : Instruction q) => o.matrix * A) (o.matrix * A) =
      ops.foldl (fun A (o : Instruction q) => o.matrix * A) (o.matrix * 1) * A
    rw [ih, ih, Matrix.mul_one, Matrix.mul_assoc]

lemma programMatrix_unitary {q : ℕ} (ops : List (Instruction q)) :
    programMatrix ops ∈ Matrix.unitaryGroup (Basis q) ℂ := by
  classical
  induction ops with
  | nil => exact one_mem _
  | cons o ops ih =>
    change ops.foldl (fun A (o : Instruction _) => o.matrix * A) (o.matrix * 1) ∈ _
    rw [programMatrix_fold, Matrix.mul_one]
    exact mul_mem ih o.unitary

lemma Circuit.apply_eq_matrix (c : Circuit) (ψ : State c.qubits) :
    c.apply ψ = (programMatrix c.instructions).mulVec ψ := by
  suffices ∀ (ops : List (Instruction c.qubits)) (ψ : State c.qubits),
      ops.foldl (fun v o => o.matrix.mulVec v) ψ = (programMatrix ops).mulVec ψ from
    this c.instructions ψ
  intro ops
  induction ops with
  | nil => intro ψ; simp [programMatrix]
  | cons o ops ih =>
    intro ψ
    rw [List.foldl_cons, ih]
    change _ = (ops.foldl (fun A (o : Instruction _) => o.matrix * A) (o.matrix * 1)).mulVec ψ
    rw [programMatrix_fold, Matrix.mul_one, Matrix.mulVec_mulVec]

/-- Reversing a listed gate stays inside the same twenty gate names. -/
def Gate.reverse (g : Gate) : Gate := {g with inverse := !g.inverse}

lemma Gate.reverse_arity (g : Gate) : g.reverse.arity = g.arity := rfl

lemma Gate.reverse_baseMatrix (g : Gate) (x y : List Bool) :
    g.reverse.baseMatrix x y = star (g.baseMatrix y x) := by
  cases h : g.inverse <;> simp [Gate.reverse, Gate.baseMatrix, h]

lemma Gate.reverse_matrix (g : Gate) (x y : List Bool) :
    g.reverse.matrix x y = star (g.matrix y x) := by
  by_cases h : g.controlled = true
  · cases x with
    | nil => cases y <;> simp [Gate.matrix, Gate.reverse, h]
    | cons a x =>
      cases y with
      | nil => simp [Gate.matrix, Gate.reverse, h]
      | cons b y =>
        cases a <;> cases b <;> simp [Gate.matrix, h, Gate.reverse]
        · by_cases hh : x = y
          · subst y; simp
          · simp [hh, Ne.symm hh]
        · simpa [Gate.reverse, h] using g.reverse_baseMatrix x y
  · have hf : g.controlled = false := Bool.eq_false_iff.mpr h
    simpa [Gate.matrix, hf, Gate.reverse] using g.reverse_baseMatrix x y

def Instruction.reverse {q : ℕ} (o : Instruction q) : Instruction q :=
  ⟨o.gate.reverse, o.wire, o.distinct⟩

lemma Instruction.reverse_matrix {q : ℕ} (o : Instruction q) :
    o.reverse.matrix = star o.matrix := by
  classical
  ext x y
  change (if ∀ i : Fin q, (∀ j, o.wire j ≠ i) → x i = y i then
      o.gate.reverse.matrix (List.ofFn (x ∘ o.wire)) (List.ofFn (y ∘ o.wire)) else 0) =
    star (if ∀ i : Fin q, (∀ j, o.wire j ≠ i) → y i = x i then
      o.gate.matrix (List.ofFn (y ∘ o.wire)) (List.ofFn (x ∘ o.wire)) else 0)
  rw [Gate.reverse_matrix]
  have he : (∀ i : Fin q, (∀ j, o.wire j ≠ i) → y i = x i) ↔
      (∀ i : Fin q, (∀ j, o.wire j ≠ i) → x i = y i) := by
    apply forall_congr'
    intro i
    exact imp_congr_right (fun _ => eq_comm)
  simp only [he]
  split_ifs <;> simp

lemma programMatrix_append {q : ℕ} (a b : List (Instruction q)) :
    programMatrix (a ++ b) = programMatrix b * programMatrix a := by
  unfold programMatrix
  rw [List.foldl_append, programMatrix_fold]
  rfl

lemma programMatrix_reverse {q : ℕ} (ops : List (Instruction q)) :
    programMatrix (ops.reverse.map Instruction.reverse) = star (programMatrix ops) := by
  induction ops with
  | nil => simp [programMatrix]
  | cons o ops ih =>
    rw [List.reverse_cons, List.map_append, programMatrix_append, ih]
    change programMatrix [o.reverse] * star (programMatrix ops) =
      star (ops.foldl (fun A (o : Instruction q) => o.matrix * A) (o.matrix * 1))
    rw [programMatrix_fold]
    simp [programMatrix, Instruction.reverse_matrix]

def Circuit.reverse (c : Circuit) : Circuit :=
  ⟨c.qubits, c.instructions.reverse.map Instruction.reverse⟩

lemma unitary_finiteInner {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (hA : A ∈ Matrix.unitaryGroup ι ℂ) (v w : ι → ℂ) :
    Exactness.finiteInner (A.mulVec v) (A.mulVec w) = Exactness.finiteInner v w := by
  change star (A.mulVec v) ⬝ᵥ A.mulVec w = star v ⬝ᵥ w
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec]
  rw [← Matrix.star_eq_conjTranspose, Matrix.mem_unitaryGroup_iff'.mp hA,
    Matrix.one_mulVec]

lemma unitary_mass {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (hA : A ∈ Matrix.unitaryGroup ι ℂ) (v : ι → ℂ) :
    (∑ x, Complex.normSq (A.mulVec v x)) = ∑ x, Complex.normSq (v x) := by
  apply Complex.ofReal_injective
  simpa [Exactness.finiteInner_self] using unitary_finiteInner A hA v v

lemma Circuit.mass (c : Circuit) (ψ : State c.qubits) :
    (∑ x, Complex.normSq (c.apply ψ x)) = ∑ x, Complex.normSq (ψ x) := by
  rw [c.apply_eq_matrix]
  exact unitary_mass _ (programMatrix_unitary _) _

lemma Circuit.output_normalized (c : Circuit) (ℓ N : ℕ) :
    (∑ x, Complex.normSq (c.outputState ℓ N x)) = 1 := by
  classical
  unfold Circuit.outputState
  rw [c.mass]
  simp

lemma Circuit.reverse_apply (c : Circuit) (ψ : State c.qubits) :
    c.reverse.apply (c.apply ψ) = ψ := by
  unfold Circuit.reverse
  rw [Circuit.apply_eq_matrix, c.apply_eq_matrix]
  change (programMatrix (c.instructions.reverse.map Instruction.reverse)).mulVec
    ((programMatrix c.instructions).mulVec ψ) = ψ
  rw [programMatrix_reverse, Matrix.mulVec_mulVec,
    Matrix.mem_unitaryGroup_iff'.mp (programMatrix_unitary _), Matrix.one_mulVec]

end ExactQuantumFactoring


end

end OAI
