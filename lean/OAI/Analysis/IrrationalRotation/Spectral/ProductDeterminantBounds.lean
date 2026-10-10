import OAI.Analysis.IrrationalRotation.Spectral.ProductDeterminant
import OAI.Analysis.IrrationalRotation.Product.ProductBlockCost

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace Invariant233.ProductModel

theorem weightedOperator_vectorDeterminant_zero_of_block_bounds
    (m : ℕ → ℕ) (hm : ∀ j, 0 < m j)
    (K C : ℕ → ℝ) (hK : ∀ j, 1 ≤ K j) (hC : ∀ j, (K j) ^ 2 ≤ C j)
    (e : ℕ ≃ Σ j, Fin (m j)) (θ : ℕ → ℝ)
    (hθ : ∀ i, θ i ∈ Set.Ico (0 : ℝ) 1) (hsum : Summable θ)
    (hlower : ∀ i, 1 / ((m (e i).1 : ℝ) * K (e i).1) ≤ θ i) :
    vectorFugledeKadisonDeterminant traceVector
      (weightedOperator θ (fun i => C (e i).1)) = 0 := by
  apply weightedOperator_vectorDeterminant_zero θ _ (fun i => (hθ i).1)
    (fun i => le_trans (sq_nonneg _) (hC (e i).1)) hsum
  exact hasNegInfiniteLogIntegral_of_block_bounds m hm K C hK hC e θ hθ hlower

end Invariant233.ProductModel

end

end OAI
