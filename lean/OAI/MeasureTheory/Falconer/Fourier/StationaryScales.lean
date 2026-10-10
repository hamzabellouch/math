import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace OAI

/-!
# Absorbing the finite stationary remainders

These are the exact scale calculations in `osc:stationary`. The ratio
`A^2 / Λ` pays for each extra stationary term. The remaining `d+2`
derivatives are absorbed using `A ≤ R^2`. No stationary-phase estimate is
assumed here.
-/

namespace Falconer

theorem stationary_remainder_ratio (J d : ℕ) (A Λ : ℝ) :
    (Λ⁻¹)^J * A^(2*J+d+2) = (A^2/Λ)^J * A^(d+2) := by
  rw [show 2*J+d+2 = 2*J+(d+2) by omega, pow_add, pow_mul, div_pow, div_eq_mul_inv]
  ring

/-- Applying a direct expansion of length `J-j` to the inverse coefficient
of order `j` has exactly the same remainder scale for every `j`. -/
theorem stationary_weighted_remainder_factor {J j : ℕ} (hj : j ≤ J)
    (d : ℕ) (A Λ : ℝ) :
    (Λ⁻¹)^j * ((Λ⁻¹)^(J-j) * A^(2*(J-j)+d+2+2*j)) =
      (Λ⁻¹)^J * A^(2*J+d+2) := by
  rw [show 2*(J-j)+d+2+2*j = 2*J+d+2 by omega, ← mul_assoc,
    ← pow_add, Nat.add_sub_of_le hj]

theorem stationary_remainder_scale (J d : ℕ) {R A Λ κ : ℝ}
    (hR : 1 ≤ R) (hA : 0 ≤ A) (hΛ : 0 < Λ) (hupper : A ≤ R^2)
    (hratio : A^2/Λ ≤ R^(-κ)) :
    (Λ⁻¹)^J * A^(2*J+d+2) ≤ R^(-κ*(J:ℝ)+2*(d+2)) := by
  have hRp : 0 < R := zero_lt_one.trans_le hR
  rw [stationary_remainder_ratio]
  calc
    _ ≤ (R^(-κ))^J * (R^2)^(d+2) :=
      mul_le_mul (pow_le_pow_left₀ (by positivity) hratio J)
        (pow_le_pow_left₀ hA hupper (d+2)) (by positivity) (by positivity)
    _ = R^(-κ*(J:ℝ)+2*(d+2)) := by
      rw [← Real.rpow_mul_natCast hRp.le, ← pow_mul,
        ← Real.rpow_natCast, ← Real.rpow_add hRp]
      congr 1
      push_cast
      ring

/-- A single finite order, independent of the large scale, achieves any
prescribed negative power. This also permits fixed derivative overhead. -/
theorem exists_stationary_remainder_order (d : ℕ) {κ T : ℝ} (hκ : 0 < κ) :
    ∃ J : ℕ, 1 ≤ J ∧ ∀ R A Λ : ℝ,
      1 ≤ R → 0 ≤ A → 0 < Λ → A ≤ R^2 → A^2/Λ ≤ R^(-κ) →
      (Λ⁻¹)^J * A^(2*J+d+2) ≤ R^(-T) := by
  obtain ⟨J,hJ⟩ := exists_nat_gt ((T+2*(d+2))/κ)
  refine ⟨J+1,by omega,?_⟩
  intro R A Λ hR hA hΛ hupper hratio
  apply (stationary_remainder_scale (J+1) d hR hA hΛ hupper hratio).trans
  apply Real.rpow_le_rpow_of_exponent_le hR
  have hJ' : T+2*(d+2) < (J:ℝ)*κ := (div_lt_iff₀ hκ).mp hJ
  push_cast
  nlinarith

end Falconer

end OAI
