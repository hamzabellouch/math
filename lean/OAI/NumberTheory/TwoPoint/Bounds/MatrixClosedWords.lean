import OAI.NumberTheory.TwoPoint.Bounds.FiniteAverages
import OAI.NumberTheory.TwoPoint.Bounds.FiniteProbability
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.Chain

namespace OAI

/-! Signed closed-word expansion of the actual matrix power moment. -/

namespace TwoPointCorrelations

open Finset

section Paths

variable {V : Type*} [Fintype V] [DecidableEq V]

def matrixPathWeight (A : Matrix V V ℝ) : {k : ℕ} → V → (Fin k → V) → ℝ
  | 0, _, _ => 1
  | _k + 1, x, v => A x (v 0) * matrixPathWeight A (v 0) (Fin.tail v)

def matrixPathEnd : {k : ℕ} → V → (Fin k → V) → V
  | 0, x, _ => x
  | _k + 1, _, v => matrixPathEnd (v 0) (Fin.tail v)

def matrixPathTerm (A : Matrix V V ℝ) {k : ℕ} (x y : V) (v : Fin k → V) : ℝ :=
  if matrixPathEnd x v = y then matrixPathWeight A x v else 0

def matrixPathVertices {k : ℕ} (x : V) (v : Fin k → V) : List V := x :: List.ofFn v

omit [Fintype V] [DecidableEq V] in
lemma matrixPathEnd_eq_last {k : ℕ} (x : V) (v : Fin (k + 1) → V) :
    matrixPathEnd x v = v (Fin.last k) := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
      change matrixPathEnd (v 0) (Fin.tail v) = _
      rw [ih]
      rfl

omit [Fintype V] in
lemma matrixPathTerm_ne_zero (A : Matrix V V ℝ) {k : ℕ} (x y : V) (v : Fin k → V)
    (h : matrixPathTerm A x y v ≠ 0) :
    matrixPathEnd x v = y ∧ matrixPathWeight A x v ≠ 0 := by
  unfold matrixPathTerm at h
  split_ifs at h with he
  · exact ⟨he, h⟩
  · contradiction

omit [Fintype V] [DecidableEq V] in
lemma matrixPathWeight_chain (A : Matrix V V ℝ) (R : V → V → Prop)
    (hA : ∀ x y, A x y ≠ 0 → R x y) {k : ℕ} (x : V) (v : Fin k → V)
    (h : matrixPathWeight A x v ≠ 0) : (matrixPathVertices x v).IsChain R := by
  induction k generalizing x with
  | zero => simp [matrixPathVertices]
  | succ k ih =>
      have hp : A x (v 0) ≠ 0 ∧ matrixPathWeight A (v 0) (Fin.tail v) ≠ 0 :=
        mul_ne_zero_iff.mp h
      have ht := ih (v 0) (Fin.tail v) hp.2
      change (x :: List.ofFn v).IsChain R
      rw [List.ofFn_succ]
      exact ht.cons_cons (hA x (v 0) hp.1)

omit [DecidableEq V] in
lemma sum_fin_cons {k : ℕ} (f : (Fin (k + 1) → V) → ℝ) :
    ∑ v, f v = ∑ a, ∑ v : Fin k → V, f (Fin.cons a v) := by
  have he := (Fin.consEquiv (fun _ : Fin (k + 1) => V)).sum_comp f
  change (∑ p : V × (Fin k → V), f (Fin.cons p.1 p.2)) = ∑ v, f v at he
  simpa only [Fintype.sum_prod_type] using he.symm

omit [Fintype V] in
lemma matrixPathTerm_cons (A : Matrix V V ℝ) {k : ℕ} (x y a : V) (v : Fin k → V) :
    matrixPathTerm A x y (Fin.cons a v) = A x a * matrixPathTerm A a y v := by
  simp only [matrixPathTerm, matrixPathEnd, matrixPathWeight, Fin.cons_zero, Fin.tail_cons]
  split_ifs <;> simp

/-- Every power entry is an exact signed sum over its successive states. -/
theorem matrix_pow_path_sum (A : Matrix V V ℝ) (k : ℕ) (x y : V) :
    (A ^ k) x y = ∑ v : Fin k → V, matrixPathTerm A x y v := by
  induction k generalizing x with
  | zero =>
      simp [matrixPathTerm, matrixPathEnd, matrixPathWeight, Matrix.one_apply]
      split_ifs <;> simp_all
  | succ k ih =>
      rw [pow_succ', Matrix.mul_apply, sum_fin_cons]
      simp_rw [ih, mul_sum, matrixPathTerm_cons]

def matrixFrobeniusSq (A : Matrix V V ℝ) : ℝ := ∑ x, ∑ y, (A x y) ^ 2

omit [DecidableEq V] in
lemma matrixFrobeniusSq_nonneg (A : Matrix V V ℝ) : 0 ≤ matrixFrobeniusSq A :=
  sum_nonneg (fun _ _ => sum_nonneg (fun _ _ => sq_nonneg _))

/-- Squaring joins two paths with the same endpoints. No absolute values
are taken in this identity, which is the step needed before centering. -/
theorem matrix_power_closed_words (A : Matrix V V ℝ) (k : ℕ) :
    matrixFrobeniusSq (A ^ k) =
      ∑ x, ∑ y, ∑ u : Fin k → V, ∑ v : Fin k → V,
        matrixPathTerm A x y u * matrixPathTerm A x y v := by
  unfold matrixFrobeniusSq
  apply sum_congr rfl
  intro x _
  apply sum_congr rfl
  intro y _
  rw [matrix_pow_path_sum, pow_two, sum_mul]
  simp_rw [mul_sum]

/-- Move the finite-law average through the full signed expansion. The
triangle inequality is applied to each word expectation only afterwards. -/
theorem average_matrix_power_le_closed_words {Ω : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω) (A : Ω → Matrix V V ℝ) (k : ℕ) :
    μ.average (fun ω => matrixFrobeniusSq (A ω ^ k)) ≤
      ∑ x, ∑ y, ∑ u : Fin k → V, ∑ v : Fin k → V,
        |μ.average (fun ω => matrixPathTerm (A ω) x y u * matrixPathTerm (A ω) x y v)| := by
  have he : μ.average (fun ω => matrixFrobeniusSq (A ω ^ k)) =
      ∑ x, ∑ y, ∑ u : Fin k → V, ∑ v : Fin k → V,
        μ.average (fun ω => matrixPathTerm (A ω) x y u * matrixPathTerm (A ω) x y v) := by
    simp only [FiniteLaw.average, matrix_power_closed_words]
    simp_rw [mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro x _
    rw [sum_comm]
    apply sum_congr rfl
    intro y _
    rw [sum_comm]
    apply sum_congr rfl
    intro u _
    rw [sum_comm]
  rw [he]
  exact sum_le_sum (fun _ _ => sum_le_sum (fun _ _ =>
    sum_le_sum (fun _ _ => sum_le_sum (fun _ _ => le_abs_self _))))

end Paths

section Nonbacktracking

variable {D V : Type*} [DecidableEq D]

/-- The manuscript's concrete block matrix `H[d,d'] = 1[d≠d'] A[d']`. -/
def blockNonbacktrackingMatrix (A : D → Matrix V V ℝ) : Matrix (D × V) (D × V) ℝ :=
  fun x y => if x.1 ≠ y.1 then A y.1 x.2 y.2 else 0

lemma blockNonbacktrackingMatrix_ne_zero (A : D → Matrix V V ℝ) (x y : D × V)
    (h : blockNonbacktrackingMatrix A x y ≠ 0) :
    x.1 ≠ y.1 ∧ A y.1 x.2 y.2 ≠ 0 := by
  unfold blockNonbacktrackingMatrix at h
  split_ifs at h with hne
  · exact ⟨hne, h⟩
  · contradiction

variable [DecidableEq V]

lemma block_path_copy_chain (A : D → Matrix V V ℝ) {k : ℕ}
    (x y : D × V) (v : Fin k → D × V)
    (hv : matrixPathTerm (blockNonbacktrackingMatrix A) x y v ≠ 0) :
    ((List.ofFn v).map Prod.fst).IsChain (fun a b => a ≠ b) := by
  have hc := matrixPathWeight_chain (blockNonbacktrackingMatrix A)
    (fun a b => a.1 ≠ b.1)
    (fun a b hab => (blockNonbacktrackingMatrix_ne_zero A a b hab).1)
    x v (matrixPathTerm_ne_zero _ x y v hv).2
  exact (List.isChain_map Prod.fst).mpr hc.tail

/-- The two halves of a nonzero closed-word term are nonbacktracking.
There is deliberately no condition across the two joins. -/
theorem closed_copy_halves_chain (A : D → Matrix V V ℝ) {k : ℕ}
    (x y : D × V) (u v : Fin k → D × V)
    (hu : matrixPathTerm (blockNonbacktrackingMatrix A) x y u ≠ 0)
    (hv : matrixPathTerm (blockNonbacktrackingMatrix A) x y v ≠ 0) :
    ((List.ofFn u).map Prod.fst).IsChain (fun a b => a ≠ b) ∧
      (((List.ofFn v).map Prod.fst).reverse).IsChain (fun a b => a ≠ b) := by
  refine ⟨block_path_copy_chain A x y u hu, ?_⟩
  exact List.isChain_reverse.mpr ((block_path_copy_chain A x y v hv).imp
    (fun _ _ hne => hne.symm))

end Nonbacktracking

end TwoPointCorrelations

end OAI
