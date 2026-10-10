import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block5Part4
import OAI.Analysis.MutuallyUnbiased.GramAssembly.FiniteSums

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block5

open scoped BigOperators

theorem row_eval_0 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node10 x =
      ∑ j : Fin 12, (weights 0 j : ℝ) * Integer.Sparse.eval (entries 0 j) x := by
  rw [node10_eval]
  exact (sum_expand_12 (fun j => (weights 0 j : ℝ) * Integer.Sparse.eval (entries 0 j) x)).symm

theorem row_eval_1 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node21 x =
      ∑ j : Fin 12, (weights 1 j : ℝ) * Integer.Sparse.eval (entries 1 j) x := by
  rw [node21_eval]
  exact (sum_expand_12 (fun j => (weights 1 j : ℝ) * Integer.Sparse.eval (entries 1 j) x)).symm

theorem row_eval_2 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node32 x =
      ∑ j : Fin 12, (weights 2 j : ℝ) * Integer.Sparse.eval (entries 2 j) x := by
  rw [node32_eval]
  exact (sum_expand_12 (fun j => (weights 2 j : ℝ) * Integer.Sparse.eval (entries 2 j) x)).symm

theorem row_eval_3 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node43 x =
      ∑ j : Fin 12, (weights 3 j : ℝ) * Integer.Sparse.eval (entries 3 j) x := by
  rw [node43_eval]
  exact (sum_expand_12 (fun j => (weights 3 j : ℝ) * Integer.Sparse.eval (entries 3 j) x)).symm

theorem row_eval_4 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node54 x =
      ∑ j : Fin 12, (weights 4 j : ℝ) * Integer.Sparse.eval (entries 4 j) x := by
  rw [node54_eval]
  exact (sum_expand_12 (fun j => (weights 4 j : ℝ) * Integer.Sparse.eval (entries 4 j) x)).symm

theorem row_eval_5 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node65 x =
      ∑ j : Fin 12, (weights 5 j : ℝ) * Integer.Sparse.eval (entries 5 j) x := by
  rw [node65_eval]
  exact (sum_expand_12 (fun j => (weights 5 j : ℝ) * Integer.Sparse.eval (entries 5 j) x)).symm

theorem row_eval_6 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node76 x =
      ∑ j : Fin 12, (weights 6 j : ℝ) * Integer.Sparse.eval (entries 6 j) x := by
  rw [node76_eval]
  exact (sum_expand_12 (fun j => (weights 6 j : ℝ) * Integer.Sparse.eval (entries 6 j) x)).symm

theorem row_eval_7 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node87 x =
      ∑ j : Fin 12, (weights 7 j : ℝ) * Integer.Sparse.eval (entries 7 j) x := by
  rw [node87_eval]
  exact (sum_expand_12 (fun j => (weights 7 j : ℝ) * Integer.Sparse.eval (entries 7 j) x)).symm

theorem row_eval_8 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node98 x =
      ∑ j : Fin 12, (weights 8 j : ℝ) * Integer.Sparse.eval (entries 8 j) x := by
  rw [node98_eval]
  exact (sum_expand_12 (fun j => (weights 8 j : ℝ) * Integer.Sparse.eval (entries 8 j) x)).symm

theorem row_eval_9 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node109 x =
      ∑ j : Fin 12, (weights 9 j : ℝ) * Integer.Sparse.eval (entries 9 j) x := by
  rw [node109_eval]
  exact (sum_expand_12 (fun j => (weights 9 j : ℝ) * Integer.Sparse.eval (entries 9 j) x)).symm

theorem row_eval_10 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node120 x =
      ∑ j : Fin 12, (weights 10 j : ℝ) * Integer.Sparse.eval (entries 10 j) x := by
  rw [node120_eval]
  exact (sum_expand_12 (fun j => (weights 10 j : ℝ) * Integer.Sparse.eval (entries 10 j) x)).symm

theorem row_eval_11 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node131 x =
      ∑ j : Fin 12, (weights 11 j : ℝ) * Integer.Sparse.eval (entries 11 j) x := by
  rw [node131_eval]
  exact (sum_expand_12 (fun j => (weights 11 j : ℝ) * Integer.Sparse.eval (entries 11 j) x)).symm

def rows (i : Fin 12) : Integer.Sparse (Fin 2886) :=
  (#[node10, node21, node32, node43, node54, node65, node76, node87, node98, node109, node120, node131]).getD i.val []

theorem rows_eval (i : Fin 12) (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval (rows i) x =
      ∑ j : Fin 12, (weights i j : ℝ) * Integer.Sparse.eval (entries i j) x := by
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
  · exact row_eval_11 x

def polynomial : Integer.Sparse (Fin 2886) := node142

theorem polynomial_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval polynomial x =
      ∑ i : Fin 12, ∑ j : Fin 12, (weights i j : ℝ) * Integer.Sparse.eval (entries i j) x := by
  calc
    _ = ∑ i : Fin 12, Integer.Sparse.eval (rows i) x := by
      rw [polynomial, node142_eval]
      exact (sum_expand_12 (fun i => Integer.Sparse.eval (rows i) x)).symm
    _ = _ := by simp_rw [rows_eval]

end MUB6.Certificate.GramAssembly.Block5

end OAI
