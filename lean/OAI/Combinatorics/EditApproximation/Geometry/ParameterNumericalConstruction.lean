import OAI.Combinatorics.EditApproximation.Geometry.ParameterConstruction
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

namespace EditApproximation



 @[simp] theorem rationalParametersWithWork_value (ell : ℕ) :
    (rationalParametersWithWork ell).1 = rationalParameters ell := by
  simp only [rationalParametersWithWork, parameterPowerWithWork_spec, rationalParameters, Nat.cast_pow]

 theorem rationalParametersWithWork_cost (ell : ℕ) :
    (rationalParametersWithWork ell).2 = 183 := by
  simp only [rationalParametersWithWork, parameterPowerWithWork_spec]



 @[simp] theorem onlineMassWithWork_value (M P H : ℕ) :
    (onlineMassWithWork M P H).1 = localOnlineMassBound M P H := by
  simp only [onlineMassWithWork, parameterPowerWithWork_spec, localOnlineMassBound]
  rw [← optimizerTriangularMass_twice, Nat.mul_div_cancel_left _ (by decide : 0 < 2)]

 theorem onlineMassWithWork_cost (M P H : ℕ) :
    (onlineMassWithWork M P H).2 = 175 := by
  simp only [onlineMassWithWork, parameterPowerWithWork_spec]



 theorem globalParameterWork_le (N : ℕ) :
    globalParameterWork N ≤ 2000 * (inputHeight N + 1) := by
  have h := integerParametersWithWork_cost N
  simp only [globalParameterWork, rationalParametersWithWork_cost, onlineMassWithWork_cost]
  omega

 theorem globalParameterWork_near_linear (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in Filter.atTop,
      (globalParameterWork N : ℝ) ≤ (N + 2 : ℝ) ^ (1 + epsilon) := by
  filter_upwards [fixed_height_power_near_linear 2 epsilon hepsilon,
    inputSmallLog_tendsto.eventually (Filter.eventually_ge_atTop 4000)] with N ht hH
  have hheight : 4000 ≤ inputHeight N := hH.trans (computed_smallLog_le_height N)
  have hscalar0 : 2000 * (inputHeight N + 1) ≤ inputHeight N ^ 2 := by
    nlinarith only [hheight]
  have hscalar : 2000 * (inputHeight N + 1) ≤ (N + 2) * inputHeight N ^ 2 :=
    hscalar0.trans (Nat.le_mul_of_pos_left _ (by omega))
  have hb : globalParameterWork N ≤ (N + 2) * inputHeight N ^ 2 :=
    (globalParameterWork_le N).trans hscalar
  exact (show (globalParameterWork N : ℝ) ≤ (N + 2 : ℝ) * (inputHeight N : ℝ) ^ 2 by
    exact_mod_cast hb).trans ht

 theorem triangularMass_word_cap (K W : ℕ)
    (hcap : Nat.size (optimizerTriangularMass K) ≤ W) : K * (K + 1) < 2 ^ (W + 1) := by
  have h := Nat.size_le.mp hcap
  rw [← optimizerTriangularMass_twice, pow_succ]
  omega

 theorem onlineMass_intermediate_word_cap (M P H W : ℕ)
    (hcap : Nat.size (localOnlineMassBound M P H) ≤ W) :
    ((H + M * (40 * P + 2) ^ 2 + 2) ^ 80) *
      ((H + M * (40 * P + 2) ^ 2 + 2) ^ 80 + 1) < 2 ^ (W + 1) :=
  triangularMass_word_cap _ W hcap

end EditApproximation

end OAI
