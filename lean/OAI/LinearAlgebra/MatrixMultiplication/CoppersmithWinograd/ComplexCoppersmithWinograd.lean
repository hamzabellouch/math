import OAI.LinearAlgebra.MatrixMultiplication.Polynomial.ComplexPolynomialApproximation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

namespace OAI

/-! Coppersmith–Winograd tensors, tensor powers and local restrictions. -/

noncomputable section

open scoped BigOperators

namespace MatrixMultiplication.Foundation
namespace CoppersmithWinograd

open Polynomial

def tensor : Tensor ℂ (Fin 3) (Fin 3) (Fin 3) :=
  fun x y z => if x.val + y.val + z.val = 2 then 1 else 0

def first : Fin 3 → Fin 3 → Polynomial ℂ
  | 0, x => C (1 / 2) * X ^ x.val
  | 1, x => C (1 / 2) * (-X) ^ x.val
  | 2, x => if x.val = 0 then -1 else 0

def other : Fin 3 → Fin 3 → Polynomial ℂ
  | 0, x => X ^ x.val
  | 1, x => (-X) ^ x.val
  | 2, x => if x.val = 0 then 1 else 0

def polynomial : Tensor (Polynomial ℂ) (Fin 3) (Fin 3) (Fin 3) :=
  fun x y z => ∑ i, Tensor.rankOne (first i) (other i) (other i) x y z

theorem rank_bound : Tensor.RankAtMost polynomial 3 :=
  ⟨first, other, other, rfl⟩

theorem polynomial_apply (x y z : Fin 3) :
    polynomial x y z =
      if x.val + y.val + z.val = 2 ∨ x.val + y.val + z.val = 4 ∨
          x.val + y.val + z.val = 6 then
        X ^ (x.val + y.val + z.val) else 0 := by
  have htwo : C (2 : ℂ) = (2 : Polynomial ℂ) := by
    calc
      _ = C ((1 : ℂ) + 1) := by norm_num
      _ = C (1 : ℂ) + C (1 : ℂ) := Polynomial.C_add
      _ = 2 := by norm_num [Polynomial.C_1]
  have hhalf : C (1 / 2 : ℂ) * 2 = (1 : Polynomial ℂ) := by
    calc
      _ = C ((1 / 2 : ℂ) * 2) := by rw [Polynomial.C_mul, htwo]
      _ = 1 := by norm_num
  have hhalf_mul (p : Polynomial ℂ) : C (1 / 2 : ℂ) * p * 2 = p := by
    calc
      _ = (C (1 / 2 : ℂ) * 2) * p := by ring
      _ = p := by rw [hhalf, one_mul]
  fin_cases x <;> fin_cases y <;> fin_cases z <;>
    norm_num [polynomial, Tensor.rankOne, first, other, Fin.sum_univ_succ] <;>
      ring_nf <;> simp only [hhalf, hhalf_mul, neg_add_cancel]

theorem leading (x y z : Fin 3) : (polynomial x y z).coeff 2 = tensor x y z := by
  fin_cases x <;> fin_cases y <;> fin_cases z <;>
    norm_num [polynomial_apply, tensor]

theorem vanishes (x y z : Fin 3) (k : ℕ) (hk : k < 2) :
    (polynomial x y z).coeff k = 0 := by
  have hcases : k = 0 ∨ k = 1 := by omega
  rcases hcases with rfl | rfl <;>
    fin_cases x <;> fin_cases y <;> fin_cases z <;>
      norm_num [polynomial_apply]

theorem degree_bound (x y z : Fin 3) : (polynomial x y z).degree ≤ 6 := by
  fin_cases x <;> fin_cases y <;> fin_cases z <;>
    norm_num [polynomial_apply]

def approximation : Tensor.PolynomialApproximation tensor 3 2 6 where
  polynomial := polynomial
  rank_bound := rank_bound
  vanishes := vanishes
  leading := leading
  degree_bound := degree_bound

theorem borderRankAtMost : Tensor.BorderRankAtMost tensor 3 :=
  approximation.borderRankAtMost

theorem rank_power (n : ℕ) :
    Tensor.RankAtMost (Tensor.power tensor n) ((6 * n + 1) * 3 ^ n) :=
  approximation.rank_power n

end CoppersmithWinograd
end MatrixMultiplication.Foundation

end

end OAI
