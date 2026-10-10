import OAI.MeasureTheory.Falconer.Recursion.ThreeIntervalShift
import Mathlib.Basic.ENNReal.Inv

namespace OAI

/-! # The actual three conditional factors, including the density penalties -/

namespace Falconer
open scoped ENNReal

theorem three_density_factor_product {R A B C η ξ : ℝ} (hR : 0 < R)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (_hC : 0 ≤ C) :
    ((ENNReal.ofReal (R^(-ξ)))⁻¹*ENNReal.ofReal (R^(10*η)*A))*
      ((ENNReal.ofReal (R^(-ξ)))⁻¹*ENNReal.ofReal B)*
      ((ENNReal.ofReal (R^(-ξ)))⁻¹*ENNReal.ofReal (R^(10*η)*C)) =
      ENNReal.ofReal (R^(20*η+3*ξ)*A*B*C) := by
  have hi : (ENNReal.ofReal (R^(-ξ)))⁻¹ = ENNReal.ofReal (R^ξ) := by
    rw [← ENNReal.ofReal_inv_of_pos (by positivity),Real.rpow_neg hR.le,inv_inv]
  rw [hi]
  rw [← ENNReal.ofReal_mul (by positivity),← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity),← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have hp : R^ξ*R^(10*η)*R^ξ*R^ξ*R^(10*η) = R^(20*η+3*ξ) := by
    rw [← Real.rpow_add hR,← Real.rpow_add hR,← Real.rpow_add hR,← Real.rpow_add hR]
    congr 1
    ring
  calc
    _ = (R^ξ*R^(10*η)*R^ξ*R^ξ*R^(10*η))*A*B*C := by ring
    _ = _ := by rw [hp]

theorem three_interval_density_product_bound {a b N J : ℕ}
    (hab : a ≤ b) (hbN : b ≤ N) (hJ : J ≤ b-a)
    {q c β γ η ξ : ℝ} (hc : 0 ≤ c)
    (hwidth : β*(N:ℝ) ≤ (b-a:ℕ))
    (hconst : ((2:ℝ)^J)^(q+c) ≤ ((2:ℝ)^N)^ξ)
    (hbudget : 20*η+4*ξ+γ ≤ c*β) :
    ((ENNReal.ofReal (((2:ℝ)^N)^(-ξ)))⁻¹*
        ENNReal.ofReal (((2:ℝ)^N)^(10*η)*((2:ℝ)^a)^(-q)))*
      ((ENNReal.ofReal (((2:ℝ)^N)^(-ξ)))⁻¹*
        ENNReal.ofReal ((1/(2:ℝ)^((b-a)-J))^(q+c)))*
      ((ENNReal.ofReal (((2:ℝ)^N)^(-ξ)))⁻¹*
        ENNReal.ofReal (((2:ℝ)^N)^(10*η)*((2:ℝ)^(N-b))^(-q))) ≤
      ENNReal.ofReal (((2:ℝ)^N)^(-q-γ)) := by
  rw [three_density_factor_product (by positivity) (by positivity) (by positivity) (by positivity)]
  exact ENNReal.ofReal_le_ofReal (three_interval_shifted_power hab hbN hJ hc hwidth hconst hbudget)

end Falconer

end OAI
