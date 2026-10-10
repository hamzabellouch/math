import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block1Part13
import OAI.Analysis.MutuallyUnbiased.GramAssembly.FiniteSums

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block1

open scoped BigOperators

theorem row_eval_0 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node19 x =
      ∑ j : Fin 21, (weights 0 j : ℝ) * Integer.Sparse.eval (entries 0 j) x := by
  rw [node19_eval]
  exact (sum_expand_21 (fun j => (weights 0 j : ℝ) * Integer.Sparse.eval (entries 0 j) x)).symm

theorem row_eval_1 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node39 x =
      ∑ j : Fin 21, (weights 1 j : ℝ) * Integer.Sparse.eval (entries 1 j) x := by
  rw [node39_eval]
  exact (sum_expand_21 (fun j => (weights 1 j : ℝ) * Integer.Sparse.eval (entries 1 j) x)).symm

theorem row_eval_2 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node59 x =
      ∑ j : Fin 21, (weights 2 j : ℝ) * Integer.Sparse.eval (entries 2 j) x := by
  rw [node59_eval]
  exact (sum_expand_21 (fun j => (weights 2 j : ℝ) * Integer.Sparse.eval (entries 2 j) x)).symm

theorem row_eval_3 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node79 x =
      ∑ j : Fin 21, (weights 3 j : ℝ) * Integer.Sparse.eval (entries 3 j) x := by
  rw [node79_eval]
  exact (sum_expand_21 (fun j => (weights 3 j : ℝ) * Integer.Sparse.eval (entries 3 j) x)).symm

theorem row_eval_4 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node99 x =
      ∑ j : Fin 21, (weights 4 j : ℝ) * Integer.Sparse.eval (entries 4 j) x := by
  rw [node99_eval]
  exact (sum_expand_21 (fun j => (weights 4 j : ℝ) * Integer.Sparse.eval (entries 4 j) x)).symm

theorem row_eval_5 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node119 x =
      ∑ j : Fin 21, (weights 5 j : ℝ) * Integer.Sparse.eval (entries 5 j) x := by
  rw [node119_eval]
  exact (sum_expand_21 (fun j => (weights 5 j : ℝ) * Integer.Sparse.eval (entries 5 j) x)).symm

theorem row_eval_6 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node139 x =
      ∑ j : Fin 21, (weights 6 j : ℝ) * Integer.Sparse.eval (entries 6 j) x := by
  rw [node139_eval]
  exact (sum_expand_21 (fun j => (weights 6 j : ℝ) * Integer.Sparse.eval (entries 6 j) x)).symm

theorem row_eval_7 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node159 x =
      ∑ j : Fin 21, (weights 7 j : ℝ) * Integer.Sparse.eval (entries 7 j) x := by
  rw [node159_eval]
  exact (sum_expand_21 (fun j => (weights 7 j : ℝ) * Integer.Sparse.eval (entries 7 j) x)).symm

theorem row_eval_8 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node179 x =
      ∑ j : Fin 21, (weights 8 j : ℝ) * Integer.Sparse.eval (entries 8 j) x := by
  rw [node179_eval]
  exact (sum_expand_21 (fun j => (weights 8 j : ℝ) * Integer.Sparse.eval (entries 8 j) x)).symm

theorem row_eval_9 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node199 x =
      ∑ j : Fin 21, (weights 9 j : ℝ) * Integer.Sparse.eval (entries 9 j) x := by
  rw [node199_eval]
  exact (sum_expand_21 (fun j => (weights 9 j : ℝ) * Integer.Sparse.eval (entries 9 j) x)).symm

theorem row_eval_10 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node219 x =
      ∑ j : Fin 21, (weights 10 j : ℝ) * Integer.Sparse.eval (entries 10 j) x := by
  rw [node219_eval]
  exact (sum_expand_21 (fun j => (weights 10 j : ℝ) * Integer.Sparse.eval (entries 10 j) x)).symm

theorem row_eval_11 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node239 x =
      ∑ j : Fin 21, (weights 11 j : ℝ) * Integer.Sparse.eval (entries 11 j) x := by
  rw [node239_eval]
  exact (sum_expand_21 (fun j => (weights 11 j : ℝ) * Integer.Sparse.eval (entries 11 j) x)).symm

theorem row_eval_12 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node259 x =
      ∑ j : Fin 21, (weights 12 j : ℝ) * Integer.Sparse.eval (entries 12 j) x := by
  rw [node259_eval]
  exact (sum_expand_21 (fun j => (weights 12 j : ℝ) * Integer.Sparse.eval (entries 12 j) x)).symm

theorem row_eval_13 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node279 x =
      ∑ j : Fin 21, (weights 13 j : ℝ) * Integer.Sparse.eval (entries 13 j) x := by
  rw [node279_eval]
  exact (sum_expand_21 (fun j => (weights 13 j : ℝ) * Integer.Sparse.eval (entries 13 j) x)).symm

theorem row_eval_14 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node299 x =
      ∑ j : Fin 21, (weights 14 j : ℝ) * Integer.Sparse.eval (entries 14 j) x := by
  rw [node299_eval]
  exact (sum_expand_21 (fun j => (weights 14 j : ℝ) * Integer.Sparse.eval (entries 14 j) x)).symm

theorem row_eval_15 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node319 x =
      ∑ j : Fin 21, (weights 15 j : ℝ) * Integer.Sparse.eval (entries 15 j) x := by
  rw [node319_eval]
  exact (sum_expand_21 (fun j => (weights 15 j : ℝ) * Integer.Sparse.eval (entries 15 j) x)).symm

theorem row_eval_16 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node339 x =
      ∑ j : Fin 21, (weights 16 j : ℝ) * Integer.Sparse.eval (entries 16 j) x := by
  rw [node339_eval]
  exact (sum_expand_21 (fun j => (weights 16 j : ℝ) * Integer.Sparse.eval (entries 16 j) x)).symm

theorem row_eval_17 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node359 x =
      ∑ j : Fin 21, (weights 17 j : ℝ) * Integer.Sparse.eval (entries 17 j) x := by
  rw [node359_eval]
  exact (sum_expand_21 (fun j => (weights 17 j : ℝ) * Integer.Sparse.eval (entries 17 j) x)).symm

theorem row_eval_18 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node379 x =
      ∑ j : Fin 21, (weights 18 j : ℝ) * Integer.Sparse.eval (entries 18 j) x := by
  rw [node379_eval]
  exact (sum_expand_21 (fun j => (weights 18 j : ℝ) * Integer.Sparse.eval (entries 18 j) x)).symm

theorem row_eval_19 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node399 x =
      ∑ j : Fin 21, (weights 19 j : ℝ) * Integer.Sparse.eval (entries 19 j) x := by
  rw [node399_eval]
  exact (sum_expand_21 (fun j => (weights 19 j : ℝ) * Integer.Sparse.eval (entries 19 j) x)).symm

theorem row_eval_20 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node419 x =
      ∑ j : Fin 21, (weights 20 j : ℝ) * Integer.Sparse.eval (entries 20 j) x := by
  rw [node419_eval]
  exact (sum_expand_21 (fun j => (weights 20 j : ℝ) * Integer.Sparse.eval (entries 20 j) x)).symm

def rows (i : Fin 21) : Integer.Sparse (Fin 2886) :=
  (#[node19, node39, node59, node79, node99, node119, node139, node159, node179, node199, node219, node239, node259, node279, node299, node319, node339, node359, node379, node399, node419]).getD i.val []

theorem rows_eval (i : Fin 21) (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval (rows i) x =
      ∑ j : Fin 21, (weights i j : ℝ) * Integer.Sparse.eval (entries i j) x := by
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
  · exact row_eval_12 x
  · exact row_eval_13 x
  · exact row_eval_14 x
  · exact row_eval_15 x
  · exact row_eval_16 x
  · exact row_eval_17 x
  · exact row_eval_18 x
  · exact row_eval_19 x
  · exact row_eval_20 x

def polynomial : Integer.Sparse (Fin 2886) := node439

theorem polynomial_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval polynomial x =
      ∑ i : Fin 21, ∑ j : Fin 21, (weights i j : ℝ) * Integer.Sparse.eval (entries i j) x := by
  calc
    _ = ∑ i : Fin 21, Integer.Sparse.eval (rows i) x := by
      rw [polynomial, node439_eval]
      exact (sum_expand_21 (fun i => Integer.Sparse.eval (rows i) x)).symm
    _ = _ := by simp_rw [rows_eval]

end MUB6.Certificate.GramAssembly.Block1

end OAI
