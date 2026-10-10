import OAI.Analysis.IrrationalRotation.Product.ProductTracialVector
import OAI.Analysis.IrrationalRotation.Spectral.ProductSpectralBundle
import OAI.Analysis.IrrationalRotation.Spectral.ProductDeterminantBounds
import OAI.Analysis.IrrationalRotation.Spectral.VectorSpectral

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace Invariant233.ProductModel

theorem weightedOperator_tracialDeterminant_eq_vector (θ c : ℕ → ℝ) :
    fugledeKadisonDeterminant (traceVector_faithfulTracial θ).toTracialState
      (⟨weightedOperator θ c, weightedOperator_mem_factor θ c⟩ : factor θ) =
        vectorFugledeKadisonDeterminant traceVector (weightedOperator θ c) :=
  (traceVector_faithfulTracial θ).determinant_eq_vector _

theorem weightedOperator_tracialDeterminant_zero_of_cost_divergence
    (θ c : ℕ → ℝ) (hθ01 : ∀ i, θ i ∈ Set.Ico (0 : ℝ) 1)
    (hc : ∀ i, 0 ≤ c i) (hθ : Summable θ)
    (hcost : (∑' i, ENNReal.ofReal (c i * θ i)) = ∞) :
    fugledeKadisonDeterminant (traceVector_faithfulTracial θ).toTracialState
      (⟨weightedOperator θ c, weightedOperator_mem_factor θ c⟩ : factor θ) = 0 := by
  rw [weightedOperator_tracialDeterminant_eq_vector]
  exact weightedOperator_vectorDeterminant_zero_of_cost_divergence θ c hθ01 hc hθ hcost

theorem weightedOperator_tracialDeterminant_zero_of_block_bounds
    (m : ℕ → ℕ) (hm : ∀ j, 0 < m j)
    (K C : ℕ → ℝ) (hK : ∀ j, 1 ≤ K j) (hC : ∀ j, (K j) ^ 2 ≤ C j)
    (e : ℕ ≃ Σ j, Fin (m j)) (θ : ℕ → ℝ)
    (hθ : ∀ i, θ i ∈ Set.Ico (0 : ℝ) 1) (hsum : Summable θ)
    (hlower : ∀ i, 1 / ((m (e i).1 : ℝ) * K (e i).1) ≤ θ i) :
    fugledeKadisonDeterminant (traceVector_faithfulTracial θ).toTracialState
      (⟨weightedOperator θ (fun i => C (e i).1),
        weightedOperator_mem_factor θ (fun i => C (e i).1)⟩ : factor θ) = 0 := by
  rw [weightedOperator_tracialDeterminant_eq_vector]
  exact weightedOperator_vectorDeterminant_zero_of_block_bounds m hm K C hK hC e θ
    hθ hsum hlower

theorem weightedOperator_factorSpectrum_eq_singleton_zero
    (θ c : ℕ → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i)
    (hθ : Summable θ) (hcost : (∑' i, ENNReal.ofReal (c i * θ i)) = ∞) :
    spectrum ℂ (⟨weightedOperator θ c,
      weightedOperator_mem_factor θ c⟩ : factor θ) = {0} := by
  have hne : (0 : factor θ) ≠ 1 := by
    intro h
    let τ := (traceVector_faithfulTracial θ).toTracialState
    have h01 : (0 : ℂ) = 1 := by
      calc
        0 = τ.toContinuousLinearMap 0 := (map_zero _).symm
        _ = τ.toContinuousLinearMap 1 := congrArg τ.toContinuousLinearMap h
        _ = 1 := τ.map_one
    exact zero_ne_one h01
  let : Nontrivial (factor θ) := ⟨⟨0, 1, hne⟩⟩
  apply spectrum_eq_singleton_zero_of_normRoot_tendsto
  exact weightedOperator_normQuasinilpotent θ c hθ0 hc hθ hcost

theorem weightedOperator_isBrownMeasure_iff_vector (θ c : ℕ → ℝ) (μ : Measure ℂ) :
    IsBrownMeasure (traceVector_faithfulTracial θ).toTracialState
      (⟨weightedOperator θ c, weightedOperator_mem_factor θ c⟩ : factor θ) μ ↔
        IsVectorBrownMeasure traceVector (weightedOperator θ c) μ :=
  (traceVector_faithfulTracial θ).isBrownMeasure_iff_vector _ μ

end Invariant233.ProductModel

end

end OAI
