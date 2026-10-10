import OAI.Analysis.IrrationalRotation.Product.ProductTracialVector
import OAI.Analysis.IrrationalRotation.Spectral.ProductQuasinilpotent
import OAI.Analysis.IrrationalRotation.Spectral.ProductDeterminant
import OAI.Analysis.IrrationalRotation.Spectral.ProductBlockQuasinilpotent
import OAI.Analysis.IrrationalRotation.Analysis.FieldShiftMoments
import OAI.Analysis.IrrationalRotation.Spectral.VectorSpectral

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace Invariant233.ProductModel

def weightedElement (θ c : ℕ → ℝ) : factor θ :=
  ⟨weightedOperator θ c, weightedOperator_mem_factor θ c⟩

def productTracialState (θ : ℕ → ℝ) : TracialState (factor θ) :=
  (traceVector_faithfulTracial θ).toTracialState

@[simp] theorem coe_weightedElement (θ c : ℕ → ℝ) :
    (weightedElement θ c : Hilbert →L[ℂ] Hilbert) = weightedOperator θ c := rfl

@[simp] theorem productTracialState_apply (θ : ℕ → ℝ) (a : factor θ) :
    productTracialState θ a = vectorTrace traceVector (a : Hilbert →L[ℂ] Hilbert) := rfl

theorem weightedElement_normQuasinilpotent (θ c : ℕ → ℝ)
    (hT : NormQuasinilpotent (weightedOperator θ c)) :
    NormQuasinilpotent (weightedElement θ c) := by
  exact hT

theorem productTracialState_weightedElement_pow_eq_zero (θ c : ℕ → ℝ)
    (n : ℕ) (hn : 0 < n) :
    productTracialState θ (weightedElement θ c ^ n) = 0 := by
  exact vectorTrace_weightedOperator_pow_eq_zero θ c n hn

theorem weightedElement_determinant_eq_vector (θ c : ℕ → ℝ) :
    fugledeKadisonDeterminant (productTracialState θ) (weightedElement θ c) =
      vectorFugledeKadisonDeterminant traceVector (weightedOperator θ c) :=
  (traceVector_faithfulTracial θ).determinant_eq_vector (weightedElement θ c)

theorem weightedElement_isBrownMeasure_iff_vector (θ c : ℕ → ℝ) (μ : Measure ℂ) :
    IsBrownMeasure (productTracialState θ) (weightedElement θ c) μ ↔
      IsVectorBrownMeasure traceVector (weightedOperator θ c) μ :=
  (traceVector_faithfulTracial θ).isBrownMeasure_iff_vector (weightedElement θ c) μ

theorem weightedElement_tracialInputs_of_logIntegral (θ c : ℕ → ℝ)
    (hθ01 : ∀ i, θ i ∈ Ico (0 : ℝ) 1) (hc : ∀ i, 0 ≤ c i)
    (hθ : Summable θ)
    (hlog : HasNegInfiniteLogIntegral baseMeasure (weight θ c)) :
    NormQuasinilpotent (weightedElement θ c) ∧
      (∀ n : ℕ, 0 < n → productTracialState θ (weightedElement θ c ^ n) = 0) ∧
      fugledeKadisonDeterminant (productTracialState θ) (weightedElement θ c) = 0 := by
  refine ⟨weightedElement_normQuasinilpotent θ c
    (weightedOperator_normQuasinilpotent_of_logIntegral θ c hθ01 hc hθ hlog),
    productTracialState_weightedElement_pow_eq_zero θ c, ?_⟩
  rw [weightedElement_determinant_eq_vector]
  exact weightedOperator_vectorDeterminant_zero θ c (fun i => (hθ01 i).1) hc hθ hlog

theorem weightedElement_tracialInputs_of_block_bounds
    (m : ℕ → ℕ) (hm : ∀ j, 0 < m j)
    (K C : ℕ → ℝ) (hK : ∀ j, 1 ≤ K j) (hC : ∀ j, K j ^ 2 ≤ C j)
    (e : ℕ ≃ Σ j, Fin (m j)) (θ : ℕ → ℝ)
    (hθ01 : ∀ i, θ i ∈ Ico (0 : ℝ) 1) (hθ : Summable θ)
    (hθlower : ∀ i, 1 / ((m (e i).1 : ℝ) * K (e i).1) ≤ θ i) :
    let c : ℕ → ℝ := fun i => C (e i).1
    NormQuasinilpotent (weightedElement θ c) ∧
      (∀ n : ℕ, 0 < n → productTracialState θ (weightedElement θ c ^ n) = 0) ∧
      fugledeKadisonDeterminant (productTracialState θ) (weightedElement θ c) = 0 := by
  exact weightedElement_tracialInputs_of_logIntegral θ _ hθ01
    (fun i => (sq_nonneg _).trans (hC (e i).1)) hθ
    (hasNegInfiniteLogIntegral_of_block_bounds m hm K C hK hC e θ hθ01 hθlower)

end Invariant233.ProductModel

end

end OAI
