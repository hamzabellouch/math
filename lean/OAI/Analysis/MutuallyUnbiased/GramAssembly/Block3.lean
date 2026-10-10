import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block3Part22
import OAI.Analysis.MutuallyUnbiased.GramAssembly.FiniteSums

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block3

open scoped BigOperators

theorem row_eval_0 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node25 x =
      ∑ j : Fin 27, (weights 0 j : ℝ) * Integer.Sparse.eval (entries 0 j) x := by
  rw [node25_eval]
  exact (sum_expand_27 (fun j => (weights 0 j : ℝ) * Integer.Sparse.eval (entries 0 j) x)).symm

theorem row_eval_1 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node51 x =
      ∑ j : Fin 27, (weights 1 j : ℝ) * Integer.Sparse.eval (entries 1 j) x := by
  rw [node51_eval]
  exact (sum_expand_27 (fun j => (weights 1 j : ℝ) * Integer.Sparse.eval (entries 1 j) x)).symm

theorem row_eval_2 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node77 x =
      ∑ j : Fin 27, (weights 2 j : ℝ) * Integer.Sparse.eval (entries 2 j) x := by
  rw [node77_eval]
  exact (sum_expand_27 (fun j => (weights 2 j : ℝ) * Integer.Sparse.eval (entries 2 j) x)).symm

theorem row_eval_3 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node103 x =
      ∑ j : Fin 27, (weights 3 j : ℝ) * Integer.Sparse.eval (entries 3 j) x := by
  rw [node103_eval]
  exact (sum_expand_27 (fun j => (weights 3 j : ℝ) * Integer.Sparse.eval (entries 3 j) x)).symm

theorem row_eval_4 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node129 x =
      ∑ j : Fin 27, (weights 4 j : ℝ) * Integer.Sparse.eval (entries 4 j) x := by
  rw [node129_eval]
  exact (sum_expand_27 (fun j => (weights 4 j : ℝ) * Integer.Sparse.eval (entries 4 j) x)).symm

theorem row_eval_5 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node155 x =
      ∑ j : Fin 27, (weights 5 j : ℝ) * Integer.Sparse.eval (entries 5 j) x := by
  rw [node155_eval]
  exact (sum_expand_27 (fun j => (weights 5 j : ℝ) * Integer.Sparse.eval (entries 5 j) x)).symm

theorem row_eval_6 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node181 x =
      ∑ j : Fin 27, (weights 6 j : ℝ) * Integer.Sparse.eval (entries 6 j) x := by
  rw [node181_eval]
  exact (sum_expand_27 (fun j => (weights 6 j : ℝ) * Integer.Sparse.eval (entries 6 j) x)).symm

theorem row_eval_7 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node207 x =
      ∑ j : Fin 27, (weights 7 j : ℝ) * Integer.Sparse.eval (entries 7 j) x := by
  rw [node207_eval]
  exact (sum_expand_27 (fun j => (weights 7 j : ℝ) * Integer.Sparse.eval (entries 7 j) x)).symm

theorem row_eval_8 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node233 x =
      ∑ j : Fin 27, (weights 8 j : ℝ) * Integer.Sparse.eval (entries 8 j) x := by
  rw [node233_eval]
  exact (sum_expand_27 (fun j => (weights 8 j : ℝ) * Integer.Sparse.eval (entries 8 j) x)).symm

theorem row_eval_9 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node259 x =
      ∑ j : Fin 27, (weights 9 j : ℝ) * Integer.Sparse.eval (entries 9 j) x := by
  rw [node259_eval]
  exact (sum_expand_27 (fun j => (weights 9 j : ℝ) * Integer.Sparse.eval (entries 9 j) x)).symm

theorem row_eval_10 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node285 x =
      ∑ j : Fin 27, (weights 10 j : ℝ) * Integer.Sparse.eval (entries 10 j) x := by
  rw [node285_eval]
  exact (sum_expand_27 (fun j => (weights 10 j : ℝ) * Integer.Sparse.eval (entries 10 j) x)).symm

theorem row_eval_11 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node311 x =
      ∑ j : Fin 27, (weights 11 j : ℝ) * Integer.Sparse.eval (entries 11 j) x := by
  rw [node311_eval]
  exact (sum_expand_27 (fun j => (weights 11 j : ℝ) * Integer.Sparse.eval (entries 11 j) x)).symm

theorem row_eval_12 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node337 x =
      ∑ j : Fin 27, (weights 12 j : ℝ) * Integer.Sparse.eval (entries 12 j) x := by
  rw [node337_eval]
  exact (sum_expand_27 (fun j => (weights 12 j : ℝ) * Integer.Sparse.eval (entries 12 j) x)).symm

theorem row_eval_13 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node363 x =
      ∑ j : Fin 27, (weights 13 j : ℝ) * Integer.Sparse.eval (entries 13 j) x := by
  rw [node363_eval]
  exact (sum_expand_27 (fun j => (weights 13 j : ℝ) * Integer.Sparse.eval (entries 13 j) x)).symm

theorem row_eval_14 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node389 x =
      ∑ j : Fin 27, (weights 14 j : ℝ) * Integer.Sparse.eval (entries 14 j) x := by
  rw [node389_eval]
  exact (sum_expand_27 (fun j => (weights 14 j : ℝ) * Integer.Sparse.eval (entries 14 j) x)).symm

theorem row_eval_15 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node415 x =
      ∑ j : Fin 27, (weights 15 j : ℝ) * Integer.Sparse.eval (entries 15 j) x := by
  rw [node415_eval]
  exact (sum_expand_27 (fun j => (weights 15 j : ℝ) * Integer.Sparse.eval (entries 15 j) x)).symm

theorem row_eval_16 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node441 x =
      ∑ j : Fin 27, (weights 16 j : ℝ) * Integer.Sparse.eval (entries 16 j) x := by
  rw [node441_eval]
  exact (sum_expand_27 (fun j => (weights 16 j : ℝ) * Integer.Sparse.eval (entries 16 j) x)).symm

theorem row_eval_17 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node467 x =
      ∑ j : Fin 27, (weights 17 j : ℝ) * Integer.Sparse.eval (entries 17 j) x := by
  rw [node467_eval]
  exact (sum_expand_27 (fun j => (weights 17 j : ℝ) * Integer.Sparse.eval (entries 17 j) x)).symm

theorem row_eval_18 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node493 x =
      ∑ j : Fin 27, (weights 18 j : ℝ) * Integer.Sparse.eval (entries 18 j) x := by
  rw [node493_eval]
  exact (sum_expand_27 (fun j => (weights 18 j : ℝ) * Integer.Sparse.eval (entries 18 j) x)).symm

theorem row_eval_19 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node519 x =
      ∑ j : Fin 27, (weights 19 j : ℝ) * Integer.Sparse.eval (entries 19 j) x := by
  rw [node519_eval]
  exact (sum_expand_27 (fun j => (weights 19 j : ℝ) * Integer.Sparse.eval (entries 19 j) x)).symm

theorem row_eval_20 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node545 x =
      ∑ j : Fin 27, (weights 20 j : ℝ) * Integer.Sparse.eval (entries 20 j) x := by
  rw [node545_eval]
  exact (sum_expand_27 (fun j => (weights 20 j : ℝ) * Integer.Sparse.eval (entries 20 j) x)).symm

theorem row_eval_21 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node571 x =
      ∑ j : Fin 27, (weights 21 j : ℝ) * Integer.Sparse.eval (entries 21 j) x := by
  rw [node571_eval]
  exact (sum_expand_27 (fun j => (weights 21 j : ℝ) * Integer.Sparse.eval (entries 21 j) x)).symm

theorem row_eval_22 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node597 x =
      ∑ j : Fin 27, (weights 22 j : ℝ) * Integer.Sparse.eval (entries 22 j) x := by
  rw [node597_eval]
  exact (sum_expand_27 (fun j => (weights 22 j : ℝ) * Integer.Sparse.eval (entries 22 j) x)).symm

theorem row_eval_23 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node623 x =
      ∑ j : Fin 27, (weights 23 j : ℝ) * Integer.Sparse.eval (entries 23 j) x := by
  rw [node623_eval]
  exact (sum_expand_27 (fun j => (weights 23 j : ℝ) * Integer.Sparse.eval (entries 23 j) x)).symm

theorem row_eval_24 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node649 x =
      ∑ j : Fin 27, (weights 24 j : ℝ) * Integer.Sparse.eval (entries 24 j) x := by
  rw [node649_eval]
  exact (sum_expand_27 (fun j => (weights 24 j : ℝ) * Integer.Sparse.eval (entries 24 j) x)).symm

theorem row_eval_25 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node675 x =
      ∑ j : Fin 27, (weights 25 j : ℝ) * Integer.Sparse.eval (entries 25 j) x := by
  rw [node675_eval]
  exact (sum_expand_27 (fun j => (weights 25 j : ℝ) * Integer.Sparse.eval (entries 25 j) x)).symm

theorem row_eval_26 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node701 x =
      ∑ j : Fin 27, (weights 26 j : ℝ) * Integer.Sparse.eval (entries 26 j) x := by
  rw [node701_eval]
  exact (sum_expand_27 (fun j => (weights 26 j : ℝ) * Integer.Sparse.eval (entries 26 j) x)).symm

def rows (i : Fin 27) : Integer.Sparse (Fin 2886) :=
  (#[node25, node51, node77, node103, node129, node155, node181, node207, node233, node259, node285, node311, node337, node363, node389, node415, node441, node467, node493, node519, node545, node571, node597, node623, node649, node675, node701]).getD i.val []

theorem rows_eval (i : Fin 27) (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval (rows i) x =
      ∑ j : Fin 27, (weights i j : ℝ) * Integer.Sparse.eval (entries i j) x := by
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
  · exact row_eval_21 x
  · exact row_eval_22 x
  · exact row_eval_23 x
  · exact row_eval_24 x
  · exact row_eval_25 x
  · exact row_eval_26 x

def polynomial : Integer.Sparse (Fin 2886) := node727

theorem polynomial_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval polynomial x =
      ∑ i : Fin 27, ∑ j : Fin 27, (weights i j : ℝ) * Integer.Sparse.eval (entries i j) x := by
  calc
    _ = ∑ i : Fin 27, Integer.Sparse.eval (rows i) x := by
      rw [polynomial, node727_eval]
      exact (sum_expand_27 (fun i => Integer.Sparse.eval (rows i) x)).symm
    _ = _ := by simp_rw [rows_eval]

end MUB6.Certificate.GramAssembly.Block3

end OAI
