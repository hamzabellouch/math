import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block4Part15
import OAI.Analysis.MutuallyUnbiased.GramAssembly.FiniteSums

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block4

open scoped BigOperators

theorem row_eval_0 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node20 x =
      ∑ j : Fin 22, (weights 0 j : ℝ) * Integer.Sparse.eval (entries 0 j) x := by
  rw [node20_eval]
  exact (sum_expand_22 (fun j => (weights 0 j : ℝ) * Integer.Sparse.eval (entries 0 j) x)).symm

theorem row_eval_1 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node41 x =
      ∑ j : Fin 22, (weights 1 j : ℝ) * Integer.Sparse.eval (entries 1 j) x := by
  rw [node41_eval]
  exact (sum_expand_22 (fun j => (weights 1 j : ℝ) * Integer.Sparse.eval (entries 1 j) x)).symm

theorem row_eval_2 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node62 x =
      ∑ j : Fin 22, (weights 2 j : ℝ) * Integer.Sparse.eval (entries 2 j) x := by
  rw [node62_eval]
  exact (sum_expand_22 (fun j => (weights 2 j : ℝ) * Integer.Sparse.eval (entries 2 j) x)).symm

theorem row_eval_3 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node83 x =
      ∑ j : Fin 22, (weights 3 j : ℝ) * Integer.Sparse.eval (entries 3 j) x := by
  rw [node83_eval]
  exact (sum_expand_22 (fun j => (weights 3 j : ℝ) * Integer.Sparse.eval (entries 3 j) x)).symm

theorem row_eval_4 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node104 x =
      ∑ j : Fin 22, (weights 4 j : ℝ) * Integer.Sparse.eval (entries 4 j) x := by
  rw [node104_eval]
  exact (sum_expand_22 (fun j => (weights 4 j : ℝ) * Integer.Sparse.eval (entries 4 j) x)).symm

theorem row_eval_5 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node125 x =
      ∑ j : Fin 22, (weights 5 j : ℝ) * Integer.Sparse.eval (entries 5 j) x := by
  rw [node125_eval]
  exact (sum_expand_22 (fun j => (weights 5 j : ℝ) * Integer.Sparse.eval (entries 5 j) x)).symm

theorem row_eval_6 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node146 x =
      ∑ j : Fin 22, (weights 6 j : ℝ) * Integer.Sparse.eval (entries 6 j) x := by
  rw [node146_eval]
  exact (sum_expand_22 (fun j => (weights 6 j : ℝ) * Integer.Sparse.eval (entries 6 j) x)).symm

theorem row_eval_7 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node167 x =
      ∑ j : Fin 22, (weights 7 j : ℝ) * Integer.Sparse.eval (entries 7 j) x := by
  rw [node167_eval]
  exact (sum_expand_22 (fun j => (weights 7 j : ℝ) * Integer.Sparse.eval (entries 7 j) x)).symm

theorem row_eval_8 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node188 x =
      ∑ j : Fin 22, (weights 8 j : ℝ) * Integer.Sparse.eval (entries 8 j) x := by
  rw [node188_eval]
  exact (sum_expand_22 (fun j => (weights 8 j : ℝ) * Integer.Sparse.eval (entries 8 j) x)).symm

theorem row_eval_9 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node209 x =
      ∑ j : Fin 22, (weights 9 j : ℝ) * Integer.Sparse.eval (entries 9 j) x := by
  rw [node209_eval]
  exact (sum_expand_22 (fun j => (weights 9 j : ℝ) * Integer.Sparse.eval (entries 9 j) x)).symm

theorem row_eval_10 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node230 x =
      ∑ j : Fin 22, (weights 10 j : ℝ) * Integer.Sparse.eval (entries 10 j) x := by
  rw [node230_eval]
  exact (sum_expand_22 (fun j => (weights 10 j : ℝ) * Integer.Sparse.eval (entries 10 j) x)).symm

theorem row_eval_11 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node251 x =
      ∑ j : Fin 22, (weights 11 j : ℝ) * Integer.Sparse.eval (entries 11 j) x := by
  rw [node251_eval]
  exact (sum_expand_22 (fun j => (weights 11 j : ℝ) * Integer.Sparse.eval (entries 11 j) x)).symm

theorem row_eval_12 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node272 x =
      ∑ j : Fin 22, (weights 12 j : ℝ) * Integer.Sparse.eval (entries 12 j) x := by
  rw [node272_eval]
  exact (sum_expand_22 (fun j => (weights 12 j : ℝ) * Integer.Sparse.eval (entries 12 j) x)).symm

theorem row_eval_13 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node293 x =
      ∑ j : Fin 22, (weights 13 j : ℝ) * Integer.Sparse.eval (entries 13 j) x := by
  rw [node293_eval]
  exact (sum_expand_22 (fun j => (weights 13 j : ℝ) * Integer.Sparse.eval (entries 13 j) x)).symm

theorem row_eval_14 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node314 x =
      ∑ j : Fin 22, (weights 14 j : ℝ) * Integer.Sparse.eval (entries 14 j) x := by
  rw [node314_eval]
  exact (sum_expand_22 (fun j => (weights 14 j : ℝ) * Integer.Sparse.eval (entries 14 j) x)).symm

theorem row_eval_15 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node335 x =
      ∑ j : Fin 22, (weights 15 j : ℝ) * Integer.Sparse.eval (entries 15 j) x := by
  rw [node335_eval]
  exact (sum_expand_22 (fun j => (weights 15 j : ℝ) * Integer.Sparse.eval (entries 15 j) x)).symm

theorem row_eval_16 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node356 x =
      ∑ j : Fin 22, (weights 16 j : ℝ) * Integer.Sparse.eval (entries 16 j) x := by
  rw [node356_eval]
  exact (sum_expand_22 (fun j => (weights 16 j : ℝ) * Integer.Sparse.eval (entries 16 j) x)).symm

theorem row_eval_17 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node377 x =
      ∑ j : Fin 22, (weights 17 j : ℝ) * Integer.Sparse.eval (entries 17 j) x := by
  rw [node377_eval]
  exact (sum_expand_22 (fun j => (weights 17 j : ℝ) * Integer.Sparse.eval (entries 17 j) x)).symm

theorem row_eval_18 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node398 x =
      ∑ j : Fin 22, (weights 18 j : ℝ) * Integer.Sparse.eval (entries 18 j) x := by
  rw [node398_eval]
  exact (sum_expand_22 (fun j => (weights 18 j : ℝ) * Integer.Sparse.eval (entries 18 j) x)).symm

theorem row_eval_19 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node419 x =
      ∑ j : Fin 22, (weights 19 j : ℝ) * Integer.Sparse.eval (entries 19 j) x := by
  rw [node419_eval]
  exact (sum_expand_22 (fun j => (weights 19 j : ℝ) * Integer.Sparse.eval (entries 19 j) x)).symm

theorem row_eval_20 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node440 x =
      ∑ j : Fin 22, (weights 20 j : ℝ) * Integer.Sparse.eval (entries 20 j) x := by
  rw [node440_eval]
  exact (sum_expand_22 (fun j => (weights 20 j : ℝ) * Integer.Sparse.eval (entries 20 j) x)).symm

theorem row_eval_21 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node461 x =
      ∑ j : Fin 22, (weights 21 j : ℝ) * Integer.Sparse.eval (entries 21 j) x := by
  rw [node461_eval]
  exact (sum_expand_22 (fun j => (weights 21 j : ℝ) * Integer.Sparse.eval (entries 21 j) x)).symm

def rows (i : Fin 22) : Integer.Sparse (Fin 2886) :=
  (#[node20, node41, node62, node83, node104, node125, node146, node167, node188, node209, node230, node251, node272, node293, node314, node335, node356, node377, node398, node419, node440, node461]).getD i.val []

theorem rows_eval (i : Fin 22) (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval (rows i) x =
      ∑ j : Fin 22, (weights i j : ℝ) * Integer.Sparse.eval (entries i j) x := by
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

def polynomial : Integer.Sparse (Fin 2886) := node482

theorem polynomial_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval polynomial x =
      ∑ i : Fin 22, ∑ j : Fin 22, (weights i j : ℝ) * Integer.Sparse.eval (entries i j) x := by
  calc
    _ = ∑ i : Fin 22, Integer.Sparse.eval (rows i) x := by
      rw [polynomial, node482_eval]
      exact (sum_expand_22 (fun i => Integer.Sparse.eval (rows i) x)).symm
    _ = _ := by simp_rw [rows_eval]

end MUB6.Certificate.GramAssembly.Block4

end OAI
