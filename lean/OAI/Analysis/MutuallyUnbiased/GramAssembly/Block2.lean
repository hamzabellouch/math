import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block2Part3
import OAI.Analysis.MutuallyUnbiased.GramAssembly.FiniteSums

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block2

open scoped BigOperators

theorem row_eval_0 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node9 x =
      ∑ j : Fin 11, (weights 0 j : ℝ) * Integer.Sparse.eval (entries 0 j) x := by
  rw [node9_eval]
  exact (sum_expand_11 (fun j => (weights 0 j : ℝ) * Integer.Sparse.eval (entries 0 j) x)).symm

theorem row_eval_1 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node19 x =
      ∑ j : Fin 11, (weights 1 j : ℝ) * Integer.Sparse.eval (entries 1 j) x := by
  rw [node19_eval]
  exact (sum_expand_11 (fun j => (weights 1 j : ℝ) * Integer.Sparse.eval (entries 1 j) x)).symm

theorem row_eval_2 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node29 x =
      ∑ j : Fin 11, (weights 2 j : ℝ) * Integer.Sparse.eval (entries 2 j) x := by
  rw [node29_eval]
  exact (sum_expand_11 (fun j => (weights 2 j : ℝ) * Integer.Sparse.eval (entries 2 j) x)).symm

theorem row_eval_3 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node39 x =
      ∑ j : Fin 11, (weights 3 j : ℝ) * Integer.Sparse.eval (entries 3 j) x := by
  rw [node39_eval]
  exact (sum_expand_11 (fun j => (weights 3 j : ℝ) * Integer.Sparse.eval (entries 3 j) x)).symm

theorem row_eval_4 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node49 x =
      ∑ j : Fin 11, (weights 4 j : ℝ) * Integer.Sparse.eval (entries 4 j) x := by
  rw [node49_eval]
  exact (sum_expand_11 (fun j => (weights 4 j : ℝ) * Integer.Sparse.eval (entries 4 j) x)).symm

theorem row_eval_5 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node59 x =
      ∑ j : Fin 11, (weights 5 j : ℝ) * Integer.Sparse.eval (entries 5 j) x := by
  rw [node59_eval]
  exact (sum_expand_11 (fun j => (weights 5 j : ℝ) * Integer.Sparse.eval (entries 5 j) x)).symm

theorem row_eval_6 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node69 x =
      ∑ j : Fin 11, (weights 6 j : ℝ) * Integer.Sparse.eval (entries 6 j) x := by
  rw [node69_eval]
  exact (sum_expand_11 (fun j => (weights 6 j : ℝ) * Integer.Sparse.eval (entries 6 j) x)).symm

theorem row_eval_7 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node79 x =
      ∑ j : Fin 11, (weights 7 j : ℝ) * Integer.Sparse.eval (entries 7 j) x := by
  rw [node79_eval]
  exact (sum_expand_11 (fun j => (weights 7 j : ℝ) * Integer.Sparse.eval (entries 7 j) x)).symm

theorem row_eval_8 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node89 x =
      ∑ j : Fin 11, (weights 8 j : ℝ) * Integer.Sparse.eval (entries 8 j) x := by
  rw [node89_eval]
  exact (sum_expand_11 (fun j => (weights 8 j : ℝ) * Integer.Sparse.eval (entries 8 j) x)).symm

theorem row_eval_9 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node99 x =
      ∑ j : Fin 11, (weights 9 j : ℝ) * Integer.Sparse.eval (entries 9 j) x := by
  rw [node99_eval]
  exact (sum_expand_11 (fun j => (weights 9 j : ℝ) * Integer.Sparse.eval (entries 9 j) x)).symm

theorem row_eval_10 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node109 x =
      ∑ j : Fin 11, (weights 10 j : ℝ) * Integer.Sparse.eval (entries 10 j) x := by
  rw [node109_eval]
  exact (sum_expand_11 (fun j => (weights 10 j : ℝ) * Integer.Sparse.eval (entries 10 j) x)).symm

def rows (i : Fin 11) : Integer.Sparse (Fin 2886) :=
  (#[node9, node19, node29, node39, node49, node59, node69, node79, node89, node99, node109]).getD i.val []

theorem rows_eval (i : Fin 11) (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval (rows i) x =
      ∑ j : Fin 11, (weights i j : ℝ) * Integer.Sparse.eval (entries i j) x := by
  fin_cases i
  · exact row_eval_0 x
  · exact row_eval_1 x
  · exact row_eval_2 x
  · exact row_eval_3 x
  · exact row_eval_4 x
  · exact row_eval_5 x
  · exact row_eval_6 x
  · exact row_eval_7 x
  · exact row_eval_8 x
  · exact row_eval_9 x
  · exact row_eval_10 x

def polynomial : Integer.Sparse (Fin 2886) := node119

theorem polynomial_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval polynomial x =
      ∑ i : Fin 11, ∑ j : Fin 11, (weights i j : ℝ) * Integer.Sparse.eval (entries i j) x := by
  calc
    _ = ∑ i : Fin 11, Integer.Sparse.eval (rows i) x := by
      rw [polynomial, node119_eval]
      exact (sum_expand_11 (fun i => Integer.Sparse.eval (rows i) x)).symm
    _ = _ := by simp_rw [rows_eval]

end MUB6.Certificate.GramAssembly.Block2

end OAI
