import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335

variable {σ ι R : Type*}

/-- All labelled paths through a nonempty sequence of matrix layers.
The empty sequence uses the usual identity-matrix path convention. -/
def matrixEntryPaths [Fintype ι] [DecidableEq ι] :
    List σ → ι → ι → List (List (σ × ι × ι))
  | [], i, j => if i = j then [[]] else []
  | [t], i, j => [[(t, i, j)]]
  | t :: u :: ts, i, j =>
      (Finset.univ.toList).flatMap fun k =>
        (matrixEntryPaths (u :: ts) k j).map fun p => (t, i, k) :: p

theorem list_sum_map_flatMap [AddMonoid R] {α β : Type*}
    (xs : List α) (f : α → List β) (g : β → R) :
    ((xs.flatMap f).map g).sum = (xs.map fun a => ((f a).map g).sum).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih]

/-- A path through `labels` chooses exactly one entry in each layer. -/
theorem matrixEntryPaths_labels [Fintype ι] [DecidableEq ι]
    (labels : List σ) (i j : ι) (p : List (σ × ι × ι))
    (hp : p ∈ matrixEntryPaths labels i j) : p.map Prod.fst = labels := by
  induction labels generalizing i p with
  | nil =>
      by_cases hij : i = j <;> simp_all [matrixEntryPaths]
  | cons t ts ih =>
      cases ts with
      | nil => simp_all [matrixEntryPaths]
      | cons u us =>
          simp only [matrixEntryPaths, List.mem_flatMap, List.mem_map] at hp
          obtain ⟨k, _, q, hq, rfl⟩ := hp
          simp [ih k q hq]

/-- Every enumerated path has one edge per layer. -/
theorem matrixEntryPaths_path_length [Fintype ι] [DecidableEq ι]
    (labels : List σ) (i j : ι) (p : List (σ × ι × ι))
    (hp : p ∈ matrixEntryPaths labels i j) : p.length = labels.length := by
  have h := congrArg List.length (matrixEntryPaths_labels labels i j p hp)
  simpa using h

/-- The number of internal-index paths through a nonempty list of layers. -/
theorem matrixEntryPaths_length [Fintype ι] [DecidableEq ι]
    (labels : List σ) (hne : labels ≠ []) (i j : ι) :
    (matrixEntryPaths labels i j).length = Fintype.card ι ^ (labels.length - 1) := by
  induction labels generalizing i with
  | nil => exact (hne rfl).elim
  | cons t ts ih =>
      cases ts with
      | nil => simp [matrixEntryPaths]
      | cons u us =>
          simp only [matrixEntryPaths, List.length_flatMap, List.length_map]
          simp_rw [ih (by simp)]
          simp [pow_succ, Nat.mul_comm]

/-- Matrix multiplication is the sum of the products along its labelled paths. -/
theorem matrixEntryPaths_sum_prod [Fintype ι] [DecidableEq ι] [Semiring R]
    (A : σ → Matrix ι ι R) (labels : List σ) (i j : ι) :
    ((matrixEntryPaths labels i j).map
      (fun p => (p.map (fun e => A e.1 e.2.1 e.2.2)).prod)).sum =
      ((labels.map A).prod) i j := by
  induction labels generalizing i with
  | nil => by_cases hij : i = j <;> simp [matrixEntryPaths, hij]
  | cons t ts ih =>
      cases ts with
      | nil => simp [matrixEntryPaths]
      | cons u us =>
          rw [matrixEntryPaths, list_sum_map_flatMap]
          simp only [List.map_map, Function.comp_def, List.map_cons, List.prod_cons]
          simp_rw [List.sum_map_mul_left, ih]
          simp [Finset.sum_map_toList, Matrix.mul_apply]

/-- Split a finite tuple into its first coordinate and its tail in a finite sum. -/
theorem sum_fin_succ_functions [Fintype ι] [AddCommMonoid R] {d : ℕ}
    (f : (Fin (d + 1) → ι) → R) :
    (∑ p, f p) = ∑ k : ι, ∑ p : Fin d → ι, f (Fin.cons k p) := by
  calc
    (∑ p, f p) = ∑ kp : ι × (Fin d → ι), f (Fin.cons kp.1 kp.2) :=
      (Equiv.sum_comp (Fin.consEquiv fun _ : Fin (d + 1) => ι) f).symm
    _ = _ := Fintype.sum_prod_type _

/-- A matrix-product entry expanded over the finite tuple of internal vertices. -/
theorem matrix_ofFn_prod_eq_sum_paths [Fintype ι] [DecidableEq ι] [Semiring R]
    (d : ℕ) (A : Fin (d + 1) → Matrix ι ι R) (i j : ι) :
    (List.ofFn A).prod i j =
      ∑ p : Fin d → ι,
        (List.ofFn fun t : Fin (d + 1) =>
          A t (Fin.cons (α := fun _ => ι) i p t) (Fin.snoc (α := fun _ => ι) p j t)).prod := by
  induction d generalizing i with
  | zero => simp [List.ofFn_succ, Fin.snoc_zero]
  | succ d ih =>
      rw [sum_fin_succ_functions]
      conv_lhs => rw [List.ofFn_succ, List.prod_cons, Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro k hk
      rw [ih, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      conv_rhs => rw [List.ofFn_succ, List.prod_cons]
      simp only [← Fin.cons_snoc_eq_snoc_cons, Fin.cons_zero, Fin.cons_succ]

/-- The labels of a path selected by its finite-list index. -/
theorem matrixEntryPaths_get_labels [Fintype ι] [DecidableEq ι]
    (labels : List σ) (i j : ι) (p : Fin (matrixEntryPaths labels i j).length) :
    ((matrixEntryPaths labels i j).get p).map Prod.fst = labels :=
  matrixEntryPaths_labels labels i j _ (List.get_mem _ p)

/-- Each list-indexed path has exactly as many edges as the list has layers. -/
theorem matrixEntryPaths_get_length [Fintype ι] [DecidableEq ι]
    (labels : List σ) (i j : ι) (p : Fin (matrixEntryPaths labels i j).length) :
    ((matrixEntryPaths labels i j).get p).length = labels.length :=
  matrixEntryPaths_path_length labels i j _ (List.get_mem _ p)

/-- The entry expansion in the finite-list-index form used by circuit gates. -/
theorem matrixEntryPaths_sum_get [Fintype ι] [DecidableEq ι] [Semiring R]
    (A : σ → Matrix ι ι R) (labels : List σ) (i j : ι) :
    (∑ p : Fin (matrixEntryPaths labels i j).length,
      (((matrixEntryPaths labels i j).get p).map
        (fun e => A e.1 e.2.1 e.2.2)).prod) = ((labels.map A).prod) i j := by
  calc
    _ = ((matrixEntryPaths labels i j).map
        (fun p => (p.map (fun e => A e.1 e.2.1 e.2.2)).prod)).sum := by
      simpa only [List.get_eq_getElem] using
        (Fin.sum_univ_fun_getElem (matrixEntryPaths labels i j)
          (fun p : List (σ × ι × ι) =>
            (p.map (fun e => A e.1 e.2.1 e.2.2)).prod))
    _ = _ := matrixEntryPaths_sum_prod A labels i j

/-- Consecutive blocks may be multiplied before multiplying the whole sequence. -/
theorem matrix_block_prod [Fintype ι] [DecidableEq ι] [Semiring R]
    (A : σ → Matrix ι ι R) (blocks : List (List σ)) :
    (blocks.map (fun block => (block.map A).prod)).prod =
      (blocks.flatten.map A).prod := by
  simp only [List.map_flatten, List.prod_flatten, List.map_map, Function.comp_def]

/-- Enumerating the block-index list and selecting blocks recovers the block list. -/
theorem map_block_get_finRange {β : Type*} (blocks : List (List σ))
    (f : List σ → β) :
    (List.finRange blocks.length).map (fun b => f (blocks.get b)) = blocks.map f := by
  conv_rhs => rw [← List.map_get_finRange blocks]
  rw [List.map_map]
  rfl

/-- Apply the path expansion to the matrix products of the consecutive blocks. -/
theorem matrix_blocks_sum_get [Fintype ι] [DecidableEq ι] [Semiring R]
    (A : σ → Matrix ι ι R) (blocks : List (List σ)) (i j : ι) :
    (∑ p : Fin (matrixEntryPaths (List.finRange blocks.length) i j).length,
      (((matrixEntryPaths (List.finRange blocks.length) i j).get p).map
        (fun e => (((blocks.get e.1).map A).prod) e.2.1 e.2.2)).prod) =
      ((blocks.flatten.map A).prod) i j := by
  have h := matrixEntryPaths_sum_get
    (fun b : Fin blocks.length => ((blocks.get b).map A).prod)
    (List.finRange blocks.length) i j
  have he := map_block_get_finRange blocks (fun block => (block.map A).prod)
  rw [he, matrix_block_prod A blocks] at h
  exact h

end Problem335

end

end OAI
