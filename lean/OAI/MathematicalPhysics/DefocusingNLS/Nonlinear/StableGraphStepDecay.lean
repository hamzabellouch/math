import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.CutoffGlobalOrbit
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.CutoffStepRemainder

namespace OAI

/-! # Endpoint decay controls the actual nonlinear path between steps -/

open Set

namespace DefocusingNLS

theorem cutoffStep_path_geometric_bound (a L M A B : ℝ)
    (hL : 0 < L) (hA : 0 ≤ A)
    (hratio : Real.exp (-(2 + a) * M / 2) ≤ 1 / 2)
    (x : ℕ → FourierL2) (V : ℕ → C(Icc (0 : ℝ) M, FourierL2))
    (hx : ∀ n, ‖x n‖ ≤ B * (1 / 2 : ℝ) ^ n)
    (hV : ∀ n, ‖V n‖ ≤ A * (‖x n‖ + (expandingRadius L ((n : ℝ) * M)) ^ (-2 - a))) :
    ∀ n, ‖V n‖ ≤ (A * (B + L ^ (-2 - a))) * (1 / 2 : ℝ) ^ n := by
  intro n
  have hp : (Real.exp (-(2 + a) * M / 2)) ^ n ≤ (1 / 2 : ℝ) ^ n :=
    pow_le_pow_left₀ (Real.exp_nonneg _) hratio n
  have hres : (expandingRadius L ((n : ℝ) * M)) ^ (-2 - a) ≤
      L ^ (-2 - a) * (1 / 2 : ℝ) ^ n := by
    rw [expandingRadius_discrete_residual a L M hL n]
    exact mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg hL.le _)
  calc
    ‖V n‖ ≤ A * (‖x n‖ + (expandingRadius L ((n : ℝ) * M)) ^ (-2 - a)) := hV n
    _ ≤ A * (B * (1 / 2 : ℝ) ^ n + L ^ (-2 - a) * (1 / 2 : ℝ) ^ n) :=
      mul_le_mul_of_nonneg_left (add_le_add (hx n) hres) hA
    _ = (A * (B + L ^ (-2 - a))) * (1 / 2 : ℝ) ^ n := by ring

end DefocusingNLS

end OAI
