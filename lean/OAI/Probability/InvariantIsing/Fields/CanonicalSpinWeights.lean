import OAI.Probability.InvariantIsing.Core.FiniteSpinEntropy
import OAI.Probability.InvariantIsing.Arrays.NSpinTensorTerminalDerivative
import OAI.Probability.InvariantIsing.Fields.FieldSpinProduct

namespace OAI

/-! The finite canonical weights used in the projection estimates are
exactly the physical Gibbs probabilities, including the uniform prior. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

theorem integral_uniformSpinGibbs_canonical {N : ℕ} (H A : Spin N → ℝ) :
    (∫ σ, A σ ∂gibbsProbability (uniformSpinPrior N : Measure (Spin N)) H) =
      ∑ σ, finiteCanonicalWeights H σ * A σ := by
  rw [integral_uniformSpinGibbs_eq]
  simp only [gibbsAverage, finiteGibbs, finitePartition, one_mul, finiteCanonicalWeights]

lemma finiteCanonicalWeights_eq_mass {N : ℕ} (H : Spin N → ℝ) (σ : Spin N) :
    finiteCanonicalWeights H σ =
      (gibbsProbability (uniformSpinPrior N : Measure (Spin N)) H).real {σ} := by
  classical
  let A := fun τ : Spin N => if τ = σ then (1 : ℝ) else 0
  have he := integral_uniformSpinGibbs_canonical H A
  have hi : (∫ τ, A τ ∂gibbsProbability (uniformSpinPrior N : Measure (Spin N)) H) =
      (gibbsProbability (uniformSpinPrior N : Measure (Spin N)) H).real {σ} := by
    simpa only [Set.indicator, Set.mem_singleton_iff, A, Pi.one_apply] using
      (integral_indicator_one (μ := gibbsProbability (uniformSpinPrior N : Measure (Spin N)) H)
        (measurableSet_singleton σ))
  rw [hi] at he
  simpa [A] using he.symm

lemma fieldCanonicalWeights_product {N : ℕ} (z : Fin N → ℝ) (σ : Spin N) :
    finiteCanonicalWeights (fieldEnergy z) σ =
      ∏ i, (scalarSpinKernel (z i)).real {σ i} := by
  rw [finiteCanonicalWeights_eq_mass, fieldSpinGibbs_eq_product, measureReal_def,
    Measure.pi_singleton, ENNReal.toReal_prod]
  rfl

end InvariantIsing

end

end OAI
