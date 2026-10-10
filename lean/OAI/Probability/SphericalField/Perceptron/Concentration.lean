import Mathlib
import OAI.Probability.SphericalField.Perceptron.Variance

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace SphericalPerceptron
open Matrix
open scoped InnerProductSpace

variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]
theorem pressure_concentrates (α β : ℝ) (hα : 0 ≤ α) (φ : ℝ →ᵇ ℝ)
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun N : ℕ => patternLaw α (N + 1)
      {g | ε < |pressure α β φ (N + 1) g - expectedPressure α β φ (N + 1)|})
      atTop (𝓝 0) := by
  have hr : Tendsto (fun N : ℕ =>
      (α * (2 * |β| * ‖φ‖) ^ 2 / (N + 1 : ℝ)) / ε ^ 2) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, one_mul, mul_zero, zero_mul] using
      (tendsto_const_nhds.mul (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))).div_const
        (ε ^ 2)
  have he := ENNReal.tendsto_ofReal hr
  simp only [ENNReal.ofReal_zero] at he
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds he
    (fun _ => bot_le) (fun N => pressure_deviation_le α β hα φ N ε hε)

theorem pressure_probability_of_expected_limit (α β : ℝ) (hα : 0 ≤ α)
    (φ : ℝ →ᵇ ℝ) (p : ℝ)
    (hp : Tendsto (fun N : ℕ => expectedPressure α β φ (N+1)) atTop (𝓝 p))
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun N : ℕ => patternLaw α (N+1)
      {g | ε < |pressure α β φ (N+1) g - p|}) atTop (𝓝 0) := by
  have he : ∀ᶠ N in atTop, |expectedPressure α β φ (N+1) - p| < ε/2 := by
    simpa only [Real.dist_eq] using (Metric.tendsto_nhds.mp hp (ε/2) (by positivity))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (pressure_concentrates α β hα φ (ε/2) (by positivity))
  · exact Filter.Eventually.of_forall fun _ => bot_le
  · filter_upwards [he] with N hN
    apply measure_mono
    intro g hg
    change ε/2 < |pressure α β φ (N+1) g - expectedPressure α β φ (N+1)|
    change ε < |pressure α β φ (N+1) g - p| at hg
    have hh := abs_sub_le (pressure α β φ (N+1) g) (expectedPressure α β φ (N+1)) p
    linarith

end SphericalPerceptron
end
end

end OAI
