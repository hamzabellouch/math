import OAI.MeasureTheory.Falconer.Recursion.ProfileIntervalChain
import OAI.MeasureTheory.Falconer.Estimates.DyadicPolynomialBudget

namespace OAI

/-! Exact growth of the finite recursive budget. The number of intervals is
fixed before the dyadic depth is sent to infinity. -/
namespace Falconer

theorem profileBudgetSequence_eq (H G W : ℝ) (n : ℕ) :
    profileBudgetSequence H G W n =
      (1024*H^3*G)^(2^n-1)*W^(2^n) := by
  induction n with
  | zero => simp [profileBudgetSequence]
  | succ n ih =>
    rw [profileBudgetSequence,ih]
    let C := 1024*H^3*G
    have hp : 1 ≤ 2^n := Nat.one_le_pow n 2 (by omega)
    calc
      _ = C*((C^(2^n-1))^2*(W^(2^n))^2) := by dsimp [profileStepBudget,C]; ring
      _ = C^(1+(2^n-1)*2)*W^((2^n)*2) := by
        rw [← pow_mul,← pow_mul,pow_add,pow_one]
        ring
      _ = _ := by
        have he : 1+(2^n-1)*2 = 2^(n+1)-1 := by rw [pow_succ]; omega
        rw [he,pow_succ]

theorem profileBudgetSequence_power_bound {H G W lam ξ : ℝ} {N : ℕ}
    (hH : 0 ≤ H) (hG : 0 ≤ G) (hW : 0 ≤ W)
    (hC : 1024*H^3*G ≤ (2:ℝ)^(ξ*(N:ℝ)))
    (hWb : W ≤ (2:ℝ)^(lam*(N:ℝ))) (n : ℕ) :
    profileBudgetSequence H G W n ≤
      (2:ℝ)^((((2^n-1:ℕ):ℝ)*ξ+((2^n:ℕ):ℝ)*lam)*(N:ℝ)) := by
  rw [profileBudgetSequence_eq]
  calc
    _ ≤ ((2:ℝ)^(ξ*(N:ℝ)))^(2^n-1)*((2:ℝ)^(lam*(N:ℝ)))^(2^n) := by
      exact mul_le_mul (pow_le_pow_left₀ (by positivity) hC _)
        (pow_le_pow_left₀ hW hWb _) (by positivity) (by positivity)
    _ = _ := by
      rw [← Real.rpow_mul_natCast (by norm_num : (0:ℝ) ≤ 2),
        ← Real.rpow_mul_natCast (by norm_num : (0:ℝ) ≤ 2),
        ← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
      congr 1
      ring

end Falconer

end OAI
