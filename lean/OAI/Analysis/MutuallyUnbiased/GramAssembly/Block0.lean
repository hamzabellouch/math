import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block0Part0
import OAI.Analysis.MutuallyUnbiased.GramAssembly.FiniteSums

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block0

open scoped BigOperators

theorem row_eval_0 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node3 x =
      ∑ j : Fin 5, (weights 0 j : ℝ) * Integer.Sparse.eval (entries 0 j) x := by
  rw [node3_eval]
  exact (sum_expand_5 (fun j => (weights 0 j : ℝ) * Integer.Sparse.eval (entries 0 j) x)).symm

theorem row_eval_1 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node7 x =
      ∑ j : Fin 5, (weights 1 j : ℝ) * Integer.Sparse.eval (entries 1 j) x := by
  rw [node7_eval]
  exact (sum_expand_5 (fun j => (weights 1 j : ℝ) * Integer.Sparse.eval (entries 1 j) x)).symm

theorem row_eval_2 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node11 x =
      ∑ j : Fin 5, (weights 2 j : ℝ) * Integer.Sparse.eval (entries 2 j) x := by
  rw [node11_eval]
  exact (sum_expand_5 (fun j => (weights 2 j : ℝ) * Integer.Sparse.eval (entries 2 j) x)).symm

theorem row_eval_3 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node15 x =
      ∑ j : Fin 5, (weights 3 j : ℝ) * Integer.Sparse.eval (entries 3 j) x := by
  rw [node15_eval]
  exact (sum_expand_5 (fun j => (weights 3 j : ℝ) * Integer.Sparse.eval (entries 3 j) x)).symm

theorem row_eval_4 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node19 x =
      ∑ j : Fin 5, (weights 4 j : ℝ) * Integer.Sparse.eval (entries 4 j) x := by
  rw [node19_eval]
  exact (sum_expand_5 (fun j => (weights 4 j : ℝ) * Integer.Sparse.eval (entries 4 j) x)).symm

def rows (i : Fin 5) : Integer.Sparse (Fin 2886) :=
  (#[node3, node7, node11, node15, node19]).getD i.val []

theorem rows_eval (i : Fin 5) (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval (rows i) x =
      ∑ j : Fin 5, (weights i j : ℝ) * Integer.Sparse.eval (entries i j) x := by
  fin_cases i
  · exact row_eval_0 x
  · exact row_eval_1 x
  · exact row_eval_2 x
  · exact row_eval_3 x
  · exact row_eval_4 x

def polynomial : Integer.Sparse (Fin 2886) := node23

theorem polynomial_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval polynomial x =
      ∑ i : Fin 5, ∑ j : Fin 5, (weights i j : ℝ) * Integer.Sparse.eval (entries i j) x := by
  calc
    _ = ∑ i : Fin 5, Integer.Sparse.eval (rows i) x := by
      rw [polynomial, node23_eval]
      exact (sum_expand_5 (fun i => Integer.Sparse.eval (rows i) x)).symm
    _ = _ := by simp_rw [rows_eval]

end MUB6.Certificate.GramAssembly.Block0

end OAI
