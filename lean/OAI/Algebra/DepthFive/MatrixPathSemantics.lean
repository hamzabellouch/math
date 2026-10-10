import OAI.Algebra.DepthFive.Basic
import OAI.Algebra.DepthFive.MatrixPaths

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335

variable {σ ι R : Type*}

/-- Replace a list by its enumeration through finite indices, under an arbitrary map. -/
theorem map_finRange_get_eq {α β : Type*} (xs : List α) (f : α → β) :
    ((List.finRange xs.length).map (fun k => f (xs.get k))) = xs.map f := by
  simpa only [List.map_map, Function.comp_def] using
    congrArg (List.map f) (List.map_get_finRange xs)

/-- Matrix-path expansion in the finite-index form used by circuit input lists. -/
theorem matrixEntryPaths_get_sum_prod [Fintype ι] [DecidableEq ι] [Semiring R]
    (A : σ → Matrix ι ι R) (labels : List σ) (i j : ι) :
    ((List.finRange (matrixEntryPaths labels i j).length).map
      (fun k => (((matrixEntryPaths labels i j).get k).map
        (fun e => A e.1 e.2.1 e.2.2)).prod)).sum =
      ((labels.map A).prod) i j := by
  rw [map_finRange_get_eq (matrixEntryPaths labels i j)
    (fun p : List (σ × ι × ι) => (p.map (fun e => A e.1 e.2.1 e.2.2)).prod)]
  exact matrixEntryPaths_sum_prod A labels i j

/-- The same expansion as a finite sum, convenient for finite-type gate constructors. -/
theorem matrixEntryPaths_fin_sum_prod [Fintype ι] [DecidableEq ι] [Semiring R]
    (A : σ → Matrix ι ι R) (labels : List σ) (i j : ι) :
    (∑ k : Fin (matrixEntryPaths labels i j).length,
      (((matrixEntryPaths labels i j).get k).map
        (fun e => A e.1 e.2.1 e.2.2)).prod) =
      ((labels.map A).prod) i j := by
  rw [← List.sum_ofFn]
  have h := congrArg
    (List.map (fun p : List (σ × ι × ι) => (p.map (fun e => A e.1 e.2.1 e.2.2)).prod))
    (List.ofFn_get (matrixEntryPaths labels i j))
  simp only [List.map_ofFn, Function.comp_def] at h
  rw [h]
  exact matrixEntryPaths_sum_prod A labels i j

/-- Every finite-indexed path contributes its label's declared degree exactly once. -/
theorem matrixEntryPaths_get_weight_sum [Fintype ι] [DecidableEq ι]
    (labels : List σ) (i j : ι) (w : σ → ℕ)
    (k : Fin (matrixEntryPaths labels i j).length) :
    ((((matrixEntryPaths labels i j).get k).map (fun e => w e.1)).sum) =
      (labels.map w).sum := by
  have h := matrixEntryPaths_labels labels i j _ (List.get_mem _ k)
  have hm := congrArg (List.map w) h
  simpa only [List.map_map, Function.comp_def] using congrArg List.sum hm

/-- Each block-entry middle gate sums precisely the variable monomials of its matrix product. -/
theorem matrixEntryPaths_get_sum_monomial (K : Type*) [CommSemiring K] (n : ℕ)
    (labels : List (Fin n)) (i j : Fin n) :
    ((List.finRange (matrixEntryPaths labels i j).length).map
      (fun k => (((matrixEntryPaths labels i j).get k).map
        (fun e => (MvPolynomial.X e : MvPolynomial (Fin n × Fin n × Fin n) K))).prod)).sum =
      ((labels.map (immLayer K n)).prod) i j := by
  exact matrixEntryPaths_get_sum_prod (immLayer K n) labels i j

end Problem335

end

end OAI
