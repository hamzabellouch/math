import Mathlib
import OAI.Probability.SKBarriers.Scalar.StationaryApproximation
import OAI.Probability.SKBarriers.Parisi.QuantileWeakCompactness
import OAI.Probability.SKBarriers.Parisi.CDFWeakLimit

namespace OAI

section

section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic

theorem exists_stationary_quantile_L1_limit (β : ℝ) :
    ∃ μ : ProbabilityMeasure ℝ, ∃ K : ℕ → ℕ,
      ∃ A : (n : ℕ) → Fin (K n+1) → ℝ,
      (μ : Measure ℝ) (Set.Icc 0 1) = 1 ∧
      (∀ n, A n ∈ admissibleQuantiles (K n)) ∧
      (∀ n B, B ∈ admissibleQuantiles (K n) →
        extendedQuantileParisi (K n) β (A n) ≤ extendedQuantileParisi (K n) β B) ∧
      (∀ n B, B ∈ admissibleQuantiles (K n) → 0 ≤ (β^2/2)*∑ j : Fin (K n+1),
        ((K n+1:ℕ):ℝ)⁻¹*(B j-A n j)*(A n j-quantileOverlapMean (K n) β (A n) j)) ∧
      Tendsto (fun n => extendedQuantileParisi (K n) β (A n)) atTop (𝓝 (finiteParisiInf β)) ∧
      Tendsto (fun n => ∫ x in Set.Icc (0:ℝ) 1,
        |quantileCDF (K n) (A n) x-cdf (μ : Measure ℝ) x|) atTop (𝓝 0) := by
  obtain ⟨K,A,hA,hm,hs,hv⟩ := exists_stationary_quantile_sequence β
  obtain ⟨μ,hμ,φ,hφ,ht⟩ := quantileProbability_weak_subsequence K A (fun n => (hA n).2)
  refine ⟨μ,fun n => K (φ n),fun n => A (φ n),hμ,fun n => hA (φ n),
    fun n => hm (φ n),fun n => hs (φ n),hv.comp hφ.tendsto_atTop,?_⟩
  have H := cdf_L1_tendsto_of_weak ht
  have he (n : ℕ) (x : ℝ) :
      cdf (quantileProbability (K (φ n)) (A (φ n)) : Measure ℝ) x =
        quantileCDF (K (φ n)) (A (φ n)) x := by
    change cdf (quantileAtomLaw (K (φ n)) (A (φ n))) x = _
    exact cdf_eq_real _ _
  simpa only [he] using H

end SK.Analytic

end
end

end

end OAI
