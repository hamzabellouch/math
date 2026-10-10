import Mathlib
import OAI.Computability.QuantumFactoring.BooleanProgram

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators Kronecker

/-- A physical placement of a register uses distinct existing qubits. -/
abbrev Register (p q : ℕ) := Fin p ↪ Fin q

namespace Register

abbrev Unused {p q : ℕ} (w : Register p q) := {i : Fin q // ∀ j, w j ≠ i}

noncomputable def split {p q : ℕ} (w : Register p q) :
    Basis q ≃ Basis p × (w.Unused → Bool) := by
  classical
  exact {
    toFun := fun x => (x ∘ w, fun i => x i.val)
    invFun := fun x i => if h : ∃ j, w j = i then x.1 h.choose
      else x.2 ⟨i, by simpa only [not_exists] using h⟩
    left_inv := by
      intro x; funext i; dsimp
      split_ifs with h
      · simp only [h.choose_spec]
      · rfl
    right_inv := by
      intro x; apply Prod.ext
      · funext j; dsimp
        have h : ∃ j', w j' = w j := ⟨j,rfl⟩
        rw [dite_eq_left h]
        exact congrArg x.1 (w.injective h.choose_spec)
      · funext i; dsimp
        rw [dite_eq_right (by simpa only [not_exists] using i.property)] }

noncomputable def liftMatrix {p q : ℕ} (w : Register p q)
    (A : Matrix (Basis p) (Basis p) ℂ) : Matrix (Basis q) (Basis q) ℂ :=
  Matrix.reindex w.split.symm w.split.symm
    (A ⊗ₖ (1 : Matrix (w.Unused → Bool) (w.Unused → Bool) ℂ))

lemma liftMatrix_one {p q : ℕ} (w : Register p q) : w.liftMatrix 1 = 1 := by
  classical
  rw [liftMatrix, Matrix.one_kronecker_one]
  exact map_one (Matrix.reindexAlgEquiv ℂ ℂ w.split.symm)

lemma liftMatrix_mul {p q : ℕ} (w : Register p q)
    (A B : Matrix (Basis p) (Basis p) ℂ) :
    w.liftMatrix (A * B) = w.liftMatrix A * w.liftMatrix B := by
  classical
  change (Matrix.reindexAlgEquiv ℂ ℂ w.split.symm)
    ((A * B) ⊗ₖ (1 : Matrix (w.Unused → Bool) (w.Unused → Bool) ℂ)) =
    (Matrix.reindexAlgEquiv ℂ ℂ w.split.symm) (A ⊗ₖ 1) *
    (Matrix.reindexAlgEquiv ℂ ℂ w.split.symm) (B ⊗ₖ 1)
  rw [← map_mul (Matrix.reindexAlgEquiv ℂ ℂ w.split.symm)]
  congr 1
  rw [← Matrix.mul_kronecker_mul, Matrix.one_mul]

lemma liftMatrix_unitary {p q : ℕ} (w : Register p q)
    (A : Matrix (Basis p) (Basis p) ℂ) (hA : A ∈ Matrix.unitaryGroup (Basis p) ℂ) :
    w.liftMatrix A ∈ Matrix.unitaryGroup (Basis q) ℂ :=
  unitary_reindex _ _ (tensor_unitary _ _ hA (one_mem _))

end Register

def Instruction.place {p q : ℕ} (w : Register p q) (o : Instruction p) : Instruction q :=
  ⟨o.gate, w ∘ o.wire, w.injective.comp o.distinct⟩

lemma Instruction.place_matrix {p q : ℕ} (w : Register p q) (o : Instruction p) :
    (o.place w).matrix = w.liftMatrix o.matrix := by
  classical
  ext x y
  let A := ∀ i : Fin q, (∀ j, w (o.wire j) ≠ i) → x i = y i
  let B := ∀ i : Fin p, (∀ j, o.wire j ≠ i) → x (w i) = y (w i)
  let C := (fun i : w.Unused => x i.val) = (fun i : w.Unused => y i.val)
  have he : A ↔ B ∧ C := by
    constructor
    · intro h
      constructor
      · intro i hi
        apply h (w i)
        intro j hh
        exact hi j (w.injective hh)
      · funext i
        apply h i.val
        intro j
        exact i.property (o.wire j)
    · rintro ⟨hB,hC⟩ i hi
      by_cases hh : ∃ j, w j = i
      · obtain ⟨j,rfl⟩ := hh
        exact hB j (fun k hk => hi k (congrArg w hk))
      · exact congrFun hC ⟨i,by simpa only [not_exists] using hh⟩
  change (if A then o.gate.matrix (List.ofFn (x ∘ w ∘ o.wire))
      (List.ofFn (y ∘ w ∘ o.wire)) else 0) =
      (if B then o.gate.matrix (List.ofFn (x ∘ w ∘ o.wire))
        (List.ofFn (y ∘ w ∘ o.wire)) else 0) * if C then 1 else 0
  simp only [he]
  split_ifs <;> simp_all

lemma programMatrix_place {p q : ℕ} (w : Register p q) (ops : List (Instruction p)) :
    programMatrix (ops.map (Instruction.place w)) = w.liftMatrix (programMatrix ops) := by
  induction ops with
  | nil => simp [programMatrix_nil, Register.liftMatrix_one]
  | cons o ops ih =>
    rw [List.map_cons, programMatrix_cons, programMatrix_cons, ih,
      Instruction.place_matrix, Register.liftMatrix_mul]

/-- Tensor states in the actual physical wire order. -/
noncomputable def Register.pairState {p q : ℕ} (w : Register p q)
    (v : State p) (z : (w.Unused → Bool) → ℂ) : State q :=
  fun x => v (w.split x).1 * z (w.split x).2

lemma Register.liftMatrix_pairState {p q : ℕ} (w : Register p q)
    (A : Matrix (Basis p) (Basis p) ℂ) (v : State p) (z : (w.Unused → Bool) → ℂ) :
    (w.liftMatrix A).mulVec (w.pairState v z) = w.pairState (A.mulVec v) z := by
  classical
  ext x
  change (∑ y, (A (w.split x).1 (w.split y).1 *
      if (w.split x).2 = (w.split y).2 then 1 else 0) *
      (v (w.split y).1 * z (w.split y).2)) =
    (∑ u, A (w.split x).1 u * v u) * z (w.split x).2
  rw [← Equiv.sum_comp w.split.symm]
  simp only [Equiv.apply_symm_apply, Fintype.sum_prod_type]
  simp [Finset.sum_mul, mul_assoc]

end ExactQuantumFactoring


end

end OAI
