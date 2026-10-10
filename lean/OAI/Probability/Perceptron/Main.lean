import Mathlib
import OAI.Probability.Perceptron.Interpolation.ReplicaMeanConst
import OAI.Probability.Perceptron.Cascade.ReweightedMomentComparison
import OAI.Probability.Perceptron.Cavity.CavityBoundedContinuous

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma expectedPressure_terminal_scaling (α β : ℝ) (φ : ℝ→ᵇℝ) (n : ℕ) :
    expectedPressure α β φ (n+1)=expectedPressure α 1 (β • φ) (n+1) := by
  unfold expectedPressure
  apply integral_congr_ae
  filter_upwards [] with g
  rw [←normalizedPatternLog_source α β φ n g,
    ←normalizedPatternLog_source α 1 (β • φ) n g,one_smul]

theorem main (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (hB : IsBrownianReal brownianEval P)
    (α β : ℝ) (hα : 0 < α) (_hβ : 0 < β) (φ : ℝ →ᵇ ℝ) :
    ∃ p : ℝ, variationalValue P α β φ = (p : EReal) ∧
      Tendsto (fun N : ℕ => expectedPressure α β φ (N + 1)) atTop (𝓝 p) ∧
      ∀ ε : ℝ, 0 < ε →
        Tendsto (fun N : ℕ => patternLaw α (N + 1)
          {g | ε < |pressure α β φ (N + 1) g - p|}) atTop (𝓝 0) := by
  let p:=(terminalVariational P α (β • φ)).toReal
  have hp : Tendsto (fun N : ℕ=>expectedPressure α β φ (N+1)) atTop (𝓝 p) := by
    have heq : (fun N : ℕ=>expectedPressure α β φ (N+1)) =
        (fun N : ℕ=>expectedPressure α 1 (β • φ) (N+1)) :=
      funext (expectedPressure_terminal_scaling α β φ)
    rw [heq]
    exact expectedPressure_limit_terminal P hB hα (β • φ)
  refine ⟨p,?_,hp,?_⟩
  · rw [variationalValue_eq_terminal]
    exact (terminalVariational_coe_toReal P α hα.le (β • φ)).symm
  · exact pressure_probability_of_expected_limit α β hα.le φ p hp

end SphericalPerceptronFreeEnergy

end

end OAI
