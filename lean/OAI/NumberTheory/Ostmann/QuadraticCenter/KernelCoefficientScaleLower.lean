import OAI.NumberTheory.Ostmann.QuadraticCenter.AmplifiedRepeatScalesBasic
import OAI.NumberTheory.Ostmann.QuadraticCenter.KernelCoefficient

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators

theorem kernelCoefficient_character_sum_lower_of_scale {P : Finset ℕ}
    (hP : ∀ p ∈ P, Nat.Prime p) (hJ : 0 < P.card)
    (ε : ℕ → ℤ) (hε : ∀ p ∈ P, ε p = -1 ∨ ε p = 1)
    {k : ℕ} (hk : 2 ≤ k) (heven : Even k) (u : ℤ)
    {c : ℝ} (hc : 0 < c)
    (hmean : c ≤ |signAverage P (fun p => ε p*jacobiSym u p)|)
    (hscale : 4*((k : ℝ)+1)^2 ≤ Real.sqrt (P.card : ℝ)*c) :
    c^k/2 ≤ ‖∑ s ∈ primeProductSamples P k,
      kernelCoefficient P ε k s*(jacobiSym u s : ℂ)‖ := by
  let a := |signAverage P (fun p => ε p*jacobiSym u p)|
  have ha : 0 < a := hc.trans_le hmean
  have herror := repeat_error_le_of_scale (by exact_mod_cast hJ) ha hk
    (hscale.trans (mul_le_mul_of_nonneg_left hmean (Real.sqrt_nonneg _)))
  have hbudget : (((k : ℝ)+1)*(k : ℝ)^2/P.card) *
      (a+(k : ℝ)/Real.sqrt (P.card : ℝ))^(k-2) ≤ a^k/2 := by
    have hp : 0 ≤ a^k := pow_nonneg ha.le _
    linarith
  exact (div_le_div_of_nonneg_right (pow_le_pow_left₀ hc.le hmean k) (by norm_num)).trans
    (kernelCoefficient_character_sum_lower_of_error_budget hP hJ ε hε hk heven u ha.le le_rfl hbudget)

end Ostmann.QuadraticCenter

end

end OAI
