import OAI.Analysis.IrrationalRotation.Product.ProductTracialInputs
import OAI.Analysis.IrrationalRotation.Spectral.QuasinilpotentBrown

namespace OAI

noncomputable section
open MeasureTheory Set

namespace Invariant233.ProductModel

private theorem factor_nontrivial_of_trace (θ : ℕ → ℝ) : Nontrivial (factor θ) := by
  refine ⟨⟨0, 1, ?_⟩⟩
  intro h
  have ht := congrArg (productTracialState θ).toContinuousLinearMap h
  rw [map_zero, (productTracialState θ).map_one] at ht
  exact zero_ne_one ht

theorem weightedOperator_isVectorBrownMeasure_dirac_zero_of_logIntegral
    (θ c : ℕ → ℝ) (hθ01 : ∀ i, θ i ∈ Ico (0 : ℝ) 1)
    (hc : ∀ i, 0 ≤ c i) (hθ : Summable θ)
    (hlog : HasNegInfiniteLogIntegral baseMeasure (weight θ c)) :
    IsVectorBrownMeasure traceVector (weightedOperator θ c) (Measure.dirac 0) := by
  let := factor_nontrivial_of_trace θ
  obtain ⟨hqn, hmom, hdet⟩ :=
    weightedElement_tracialInputs_of_logIntegral θ c hθ01 hc hθ hlog
  exact (weightedElement_isBrownMeasure_iff_vector θ c _).mp
    (isBrownMeasure_dirac_zero_of_normQuasinilpotent_of_moments_zero
      (productTracialState θ) hqn hmom hdet)

theorem weightedOperator_isVectorBrownMeasure_dirac_zero_of_block_bounds
    (m : ℕ → ℕ) (hm : ∀ j, 0 < m j)
    (K C : ℕ → ℝ) (hK : ∀ j, 1 ≤ K j) (hC : ∀ j, K j ^ 2 ≤ C j)
    (e : ℕ ≃ Σ j, Fin (m j)) (θ : ℕ → ℝ)
    (hθ01 : ∀ i, θ i ∈ Ico (0 : ℝ) 1) (hθ : Summable θ)
    (hθlower : ∀ i, 1 / ((m (e i).1 : ℝ) * K (e i).1) ≤ θ i) :
    IsVectorBrownMeasure traceVector
      (weightedOperator θ (fun i => C (e i).1)) (Measure.dirac 0) := by
  let := factor_nontrivial_of_trace θ
  obtain ⟨hqn, hmom, hdet⟩ := weightedElement_tracialInputs_of_block_bounds
    m hm K C hK hC e θ hθ01 hθ hθlower
  exact (weightedElement_isBrownMeasure_iff_vector θ _ _).mp
    (isBrownMeasure_dirac_zero_of_normQuasinilpotent_of_moments_zero
      (productTracialState θ) hqn hmom hdet)

end Invariant233.ProductModel

end

end OAI
