import OAI.LinearAlgebra.MatrixMultiplication.Tensor.BaseTensors
import OAI.LinearAlgebra.MatrixMultiplication.Completion.RecursiveCompletion

namespace OAI

/-! Finite coefficient tensors and their algebraic transformations. -/

noncomputable section

namespace MatrixMultiplication

open MatrixMultiplication.Foundation Polynomial
open scoped BigOperators Classical

namespace BaseTwo

def first (i x : Fin 2) : Polynomial ℂ :=
  if i = 0 then X ^ x.val else if x = 0 then -1 else 0

def other (i x : Fin 2) : Polynomial ℂ :=
  if i = 0 then X ^ x.val else if x = 0 then 1 else 0

def polynomial : Tensor (Polynomial ℂ) (Fin 2) (Fin 2) (Fin 2) :=
  fun x y z => ∑ i, Tensor.rankOne (first i) (other i) (other i) x y z

theorem polynomial_rank : Tensor.RankAtMost polynomial 2 :=
  ⟨first, other, other, rfl⟩

theorem polynomial_difference (x y z : Fin 2) :
    polynomial x y z =
      X ^ x.val * X ^ y.val * X ^ z.val -
        (if x = 0 then 1 else 0) * (if y = 0 then 1 else 0) *
          (if z = 0 then 1 else 0) := by
  simp only [polynomial, Fin.sum_univ_two]
  fin_cases x <;> fin_cases y <;> fin_cases z <;>
    norm_num [Fin.ext_iff, first, other, Tensor.rankOne]

theorem polynomial_apply (x y z : Fin 2) :
    polynomial x y z =
      if x.val + y.val + z.val = 0 then 0 else X ^ (x.val + y.val + z.val) := by
  fin_cases x <;> fin_cases y <;> fin_cases z <;>
    norm_num [Fin.ext_iff, polynomial_difference] <;> ring

theorem polynomial_coeff (x y z : Fin 2) (k : ℕ) :
    (polynomial x y z).coeff k =
      if x.val + y.val + z.val ≠ 0 ∧ k = x.val + y.val + z.val then 1 else 0 := by
  rw [polynomial_apply]
  by_cases hs : x.val + y.val + z.val = 0
  · simp only [hs, ite_true, ne_eq, not_true_eq_false, false_and, ite_false,
      Polynomial.coeff_zero]
  · simp only [hs, ite_false, ne_eq, not_false_eq_true, true_and, Polynomial.coeff_X_pow]

theorem polynomial_leading (x y z : Fin 2) :
    (polynomial x y z).coeff 1 = tensor x y z := by
  fin_cases x <;> fin_cases y <;> fin_cases z <;>
    norm_num [Fin.ext_iff, polynomial_apply, tensor]

theorem polynomial_vanishes (x y z : Fin 2) (k : ℕ) (hk : k < 1) :
    (polynomial x y z).coeff k = 0 := by
  have hk0 : k = 0 := by omega
  subst k
  fin_cases x <;> fin_cases y <;> fin_cases z <;> norm_num [Fin.ext_iff, polynomial_apply]

theorem polynomial_degree (x y z : Fin 2) :
    (polynomial x y z).degree ≤ 3 := by
  fin_cases x <;> fin_cases y <;> fin_cases z <;> norm_num [Fin.ext_iff, polynomial_apply]

def approximation : Tensor.PolynomialApproximation tensor 2 1 3 where
  polynomial := polynomial
  rank_bound := polynomial_rank
  vanishes := polynomial_vanishes
  leading := polynomial_leading
  degree_bound := polynomial_degree

def flagged : FlaggedTensor (Fin 2) (Fin 2) (Fin 2) where
  tensor := tensor
  flagB := flagB
  flagA := flagA
  flagC := flagC
  one_hot := one_hot

def leafColor (i : Fin 3) : Color := if i = 0 then .B else if i = 1 then .A else .C

theorem leafColor_owner (i : Fin 3) :
    (leafColor i = .B ↔ flagB (point i).1) ∧
    (leafColor i = .A ↔ flagA (point i).2.2) ∧
    (leafColor i = .C ↔ flagC (point i).2.1) := by
  fin_cases i <;> norm_num [Fin.ext_iff, leafColor, point, flagB, flagA, flagC]

def powerApproximation (n : ℕ) :
    Tensor.PolynomialApproximation (Tensor.power flagged.tensor n) (2 ^ n) n (3 * n) := by
  simpa only [Nat.one_mul, flagged] using approximation.power n

theorem rank_power (n : ℕ) :
    Tensor.RankAtMost (Tensor.power tensor n) ((3 * n + 1) * 2 ^ n) :=
  approximation.rank_power n

theorem borderRankAtMost : Tensor.BorderRankAtMost tensor 2 :=
  approximation.borderRankAtMost

end BaseTwo

namespace BaseThree

def polynomial : Tensor (Polynomial ℂ) (Fin 3) (Fin 3) (Fin 3) :=
  CWPrimitiveDegeneration.boundaryApproximation.polynomial

theorem polynomial_apply (x y z : Fin 3) :
    polynomial x y z =
      if x.val + y.val + z.val = 2 ∨ x.val + y.val + z.val = 4 ∨
          x.val + y.val + z.val = 6 then
        X ^ (2 * (x.val + y.val + z.val) + CWBoundary.weight x y z) else 0 :=
  CWPrimitiveDegeneration.boundaryApproximation_polynomial_apply x y z

theorem polynomial_leading (x y z : Fin 3) :
    (polynomial x y z).coeff 5 = tensor x y z := by
  fin_cases x <;> fin_cases y <;> fin_cases z <;>
    norm_num [Fin.ext_iff, polynomial_apply, CWBoundary.weight, tensor, CWBoundary.tensor,
      CoppersmithWinograd.tensor]

theorem polynomial_vanishes (x y z : Fin 3) (k : ℕ) (hk : k < 5) :
    (polynomial x y z).coeff k = 0 := by
  have hk5 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
  rcases hk5 with rfl | rfl | rfl | rfl | rfl <;>
    fin_cases x <;> fin_cases y <;> fin_cases z <;>
      norm_num [Fin.ext_iff, polynomial_apply, CWBoundary.weight]

theorem polynomial_degree (x y z : Fin 3) :
    (polynomial x y z).degree ≤ 15 := by
  fin_cases x <;> fin_cases y <;> fin_cases z <;>
    norm_num [Fin.ext_iff, polynomial_apply, CWBoundary.weight]

def approximation : Tensor.PolynomialApproximation tensor 3 5 15 where
  polynomial := polynomial
  rank_bound := CWPrimitiveDegeneration.boundaryApproximation.rank_bound
  vanishes := polynomial_vanishes
  leading := polynomial_leading
  degree_bound := polynomial_degree

def flagged : FlaggedTensor (Fin 3) (Fin 3) (Fin 3) where
  tensor := tensor
  flagB := flagB
  flagA := flagA
  flagC := flagC
  one_hot := one_hot

def leafColor (i : Fin 5) : Color := if i.val < 2 then .A else if i.val < 4 then .B else .C

theorem leafColor_owner (i : Fin 5) :
    (leafColor i = .B ↔ flagB (point i).1) ∧
    (leafColor i = .A ↔ flagA (point i).2.2) ∧
    (leafColor i = .C ↔ flagC (point i).2.1) := by
  fin_cases i <;> norm_num [Fin.ext_iff, leafColor, point, flagB, flagA, flagC]

def powerApproximation (n : ℕ) :
    Tensor.PolynomialApproximation (Tensor.power flagged.tensor n)
      (3 ^ n) (5 * n) (15 * n) := approximation.power n

theorem rank_power (n : ℕ) :
    Tensor.RankAtMost (Tensor.power tensor n) ((15 * n + 1) * 3 ^ n) :=
  approximation.rank_power n

theorem borderRankAtMost : Tensor.BorderRankAtMost tensor 3 :=
  approximation.borderRankAtMost

end BaseThree
end MatrixMultiplication

end

end OAI
