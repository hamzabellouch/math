import OAI.Analysis.IrrationalRotation.Product.ProductFieldConverse
import OAI.Analysis.IrrationalRotation.Product.ProductDiffuse
import OAI.Analysis.IrrationalRotation.Analysis.ConcretePredualModels

namespace OAI

noncomputable section
namespace Invariant233.ProductModel

theorem factor_complete (θ : ℕ → ℝ)
    (hθ : ProductModel.JointlyRationallyIndependent θ) :
    IsTypeII1FactorWithVector (ProductModel.factor θ) ProductModel.traceVector ∧
      HasSeparablePredual (ProductModel.factor θ) ∧
      (∀ A : ProductModel.Hilbert →L[ℂ] ProductModel.Hilbert,
        A ∈ ProductModel.factor θ ↔
          ∃ (F : ProductModel.Base → ProductModel.Fiber →L[ℂ] ProductModel.Fiber)
            (B : ℝ), ProductModel.IsCovariantFieldRepresentation θ A F B) ∧
      (∀ (A : ProductModel.Hilbert →L[ℂ] ProductModel.Hilbert)
        (F : ProductModel.Base → ProductModel.Fiber →L[ℂ] ProductModel.Fiber) (B : ℝ),
        ProductModel.IsCovariantFieldRepresentation θ A F B →
          vectorTrace ProductModel.traceVector A = ProductModel.centralDiagonalIntegral F) := by
  refine ⟨factor_isTypeII1FactorWithVector θ hθ,
    factor_hasSeparablePredual θ,
    mem_factor_iff_covariantFieldRepresentation θ, ?_⟩
  intro A F B h
  exact h.vectorTrace_eq

end Invariant233.ProductModel

end

end OAI
