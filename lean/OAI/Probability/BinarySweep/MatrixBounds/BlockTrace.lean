import Mathlib
import OAI.Probability.BinarySweep.MatrixBounds.TraceHolder

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator

namespace BinaryCoordinateSweeps.TraceHolder

section Expansion
variable {P R : Type*} [Fintype P] [DecidableEq P] [Semiring R]

def pathProduct {n : ℕ} (A : Fin n → Matrix P P R) (x : Fin n → P) (b : P) : R :=
  (List.ofFn fun j => A j (x j) (Fin.snoc (α := fun _ => P) x b j.succ)).prod

omit [Fintype P] [DecidableEq P] in
lemma snoc_cons_succ {n : ℕ} (a : P) (x : Fin n → P) (b : P) (j : Fin (n+1)) :
    Fin.snoc (α := fun _ => P) (Fin.cons a x) b j.succ =
      Fin.snoc (α := fun _ => P) x b j := by
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp
  · rw [Fin.succ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.cons_succ]

omit [Fintype P] [DecidableEq P] in
lemma pathProduct_cons {n : ℕ} (A : Fin (n+1) → Matrix P P R)
    (a : P) (x : Fin n → P) (b : P) :
    pathProduct A (Fin.cons a x) b =
      A 0 a (Fin.snoc (α := fun _ => P) x b 0) * pathProduct (fun j => A j.succ) x b := by
  simp only [pathProduct, List.ofFn_succ, List.prod_cons, Fin.cons_zero, Fin.cons_succ,
    snoc_cons_succ]

lemma prod_apply_sum_path {n : ℕ} (A : Fin (n+1) → Matrix P P R) (a b : P) :
    (List.ofFn A).prod a b = ∑ x : Fin n → P, pathProduct A (Fin.cons a x) b := by
  induction n generalizing a with
  | zero => simp [pathProduct, Fin.snoc]
  | succ n ih =>
      rw [List.ofFn_succ, List.prod_cons, Matrix.mul_apply]
      simp_rw [ih]
      rw [← (Fin.consEquiv (fun _ : Fin (n+1) => P)).sum_comp, Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro c _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      change A 0 a c * pathProduct (fun j => A j.succ) (Fin.cons c x) b =
        pathProduct A (Fin.cons a (Fin.cons c x)) b
      rw [pathProduct_cons A]
      congr 2

omit [Fintype P] [DecidableEq P] in
lemma snoc_cycle {n : ℕ} (x : Fin (n+1) → P) (j : Fin (n+1)) :
    Fin.snoc (α := fun _ => P) x (x 0) j.succ = x (finRotate (n+1) j) := by
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp
  · rw [Fin.succ_castSucc, Fin.snoc_castSucc]
    simp [finRotate_apply, Fin.coeSucc_eq_succ]

lemma trace_prod_eq_sum_cycles {n : ℕ} (A : Fin (n+1) → Matrix P P R) :
    Matrix.trace (List.ofFn A).prod =
      ∑ x : Fin (n+1) → P,
        (List.ofFn fun j => A j (x j) (x (finRotate (n+1) j))).prod := by
  change (∑ i : P, (List.ofFn A).prod i i) = _
  simp_rw [prod_apply_sum_path]
  calc
    _ = ∑ y : P × (Fin n → P), pathProduct A (Fin.cons y.1 y.2) y.1 := by
      exact (Fintype.sum_prod_type (fun y : P × (Fin n → P) =>
        pathProduct A (Fin.cons y.1 y.2) y.1)).symm
    _ = ∑ x : Fin (n+1) → P, pathProduct A x (x 0) := by
      simpa only [Fin.consEquiv, Equiv.coe_fn_mk, Fin.cons_zero] using
        (Fin.consEquiv (fun _ : Fin (n+1) => P)).sum_comp (fun x => pathProduct A x (x 0))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x _
      simp only [pathProduct, snoc_cycle]
end Expansion

variable {P ι : Type*} [Fintype P] [DecidableEq P] [Fintype ι] [DecidableEq ι]

def flattenBlocks (A : Matrix P P (M ι)) : M (P × ι) :=
  fun x y => A x.1 y.1 x.2 y.2

omit [DecidableEq P] [DecidableEq ι] in
lemma flattenBlocks_mul (A B : Matrix P P (M ι)) :
    flattenBlocks (A * B) = flattenBlocks A * flattenBlocks B := by
  ext x y
  simp only [flattenBlocks, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.sum_apply]

omit [Fintype P] [Fintype ι] in
lemma flattenBlocks_one : flattenBlocks (1 : Matrix P P (M ι)) = 1 := by
  ext ⟨x,i⟩ ⟨y,j⟩
  by_cases hxy : x = y <;> by_cases hij : i = j <;>
    simp [flattenBlocks, Matrix.one_apply, hxy, hij, Prod.mk.injEq]

def flattenBlocksHom : Matrix P P (M ι) →* M (P × ι) where
  toFun := flattenBlocks
  map_one' := flattenBlocks_one
  map_mul' := flattenBlocks_mul

omit [DecidableEq P] [DecidableEq ι] in
lemma trace_flattenBlocks (A : Matrix P P (M ι)) :
    Matrix.trace (flattenBlocks A) = Matrix.trace (Matrix.trace A) := by
  change (∑ x : P × ι, A x.1 x.1 x.2 x.2) = ∑ i : ι, (∑ p : P, A p p) i i
  simp only [Fintype.sum_prod_type, Matrix.sum_apply]
  exact Finset.sum_comm

lemma trace_flatten_prod {n : ℕ} (A : Fin (n+1) → Matrix P P (M ι)) :
    Matrix.trace (List.ofFn (fun j => flattenBlocks (A j))).prod =
      ∑ x : Fin (n+1) → P,
        Matrix.trace (List.ofFn fun j => A j (x j) (x (finRotate (n+1) j))).prod := by
  have hp : (List.ofFn (fun j => flattenBlocks (A j))).prod =
      flattenBlocks (List.ofFn A).prod := by
    simpa only [List.map_ofFn, flattenBlocksHom, MonoidHom.coe_mk, OneHom.coe_mk, Function.comp_def] using
      (map_list_prod (flattenBlocksHom (P := P) (ι := ι)) (List.ofFn A)).symm
  rw [hp, trace_flattenBlocks, trace_prod_eq_sum_cycles, Matrix.trace_sum]

theorem block_trace_holder {q : ℕ} (hq : 0 < q)
    (A : Fin (2*q) → Matrix P P (M ι)) :
    ‖Matrix.trace (List.ofFn (fun j => flattenBlocks (A j))).prod‖ ≤
      ∑ x : Fin (2*q) → P,
        ∏ j, matrixMoment q (A j (x j) (x (finRotate (2*q) j))) ^ (((2*q : ℕ) : ℝ)⁻¹) := by
  have ht : Matrix.trace (List.ofFn (fun j => flattenBlocks (A j))).prod =
      ∑ x : Fin (2*q) → P,
        Matrix.trace (List.ofFn fun j => A j (x j) (x (finRotate (2*q) j))).prod := by
    generalize hm : 2*q = m at A ⊢
    cases m with
    | zero => omega
    | succ n => exact trace_flatten_prod A
  rw [ht]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => matrix_trace_holder hq _)

theorem weighted_block_trace_holder {q : ℕ} (hq : 0 < q)
    (p : Fin (2*q) → P → P → ℝ) (hp : ∀ j x y, 0 ≤ p j x y)
    (F : Fin (2*q) → P → P → M ι) :
    ‖Matrix.trace (List.ofFn fun j => flattenBlocks
      (fun x y => p j x y • F j x y)).prod‖ ≤
      ∑ x : Fin (2*q) → P,
        (∏ j, p j (x j) (x (finRotate (2*q) j))) *
        ∏ j, matrixMoment q (F j (x j) (x (finRotate (2*q) j))) ^ (((2*q : ℕ) : ℝ)⁻¹) := by
  have ht : Matrix.trace (List.ofFn fun j => flattenBlocks
      (fun x y => p j x y • F j x y)).prod =
      ∑ x : Fin (2*q) → P,
        Matrix.trace (List.ofFn fun j => p j (x j) (x (finRotate (2*q) j)) •
          F j (x j) (x (finRotate (2*q) j))).prod := by
    generalize hm : 2*q = m at p F ⊢
    cases m with
    | zero => omega
    | succ n => exact trace_flatten_prod _
  rw [ht]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro x _
  rw [prod_ofFn_smul, Matrix.trace_smul, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (Finset.prod_nonneg (fun j _ => hp j _ _))]
  exact mul_le_mul_of_nonneg_left (matrix_trace_holder hq _)
    (Finset.prod_nonneg (fun j _ => hp j _ _))

end BinaryCoordinateSweeps.TraceHolder

end

end OAI
