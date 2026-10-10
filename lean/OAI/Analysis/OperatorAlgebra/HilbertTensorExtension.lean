import OAI.Analysis.Nuclearity.MinimalTensorExtension
import OAI.Analysis.WeakInfiniteness.CrossUniverseTensorMap

namespace OAI

/-! Finite-sum bounds and minimal tensor completion, with the Hilbert
operator structure fixed before a concrete representation is substituted. -/
noncomputable section
open scoped TensorProduct
namespace WeakPureInfiniteness

lemma minimalSum_map_norm_le {A B C D : Type*}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    [NonUnitalCStarAlgebra C] [NonUnitalCStarAlgebra D]
    (φ : A →⋆ₙₐ[ℂ] C) (ψ : B →⋆ₙₐ[ℂ] D)
    {I : Type*} [Fintype I] (a : I → A) (b : I → B) :
    ‖∑ i, minimalElementary (φ (a i)) (ψ (b i))‖ ≤
      ‖∑ i, minimalElementary (a i) (b i)‖ := by
  have h := NonUnitalStarAlgHom.norm_apply_le (minimalMapAny φ ψ)
    (∑ i, minimalElementary (a i) (b i))
  simpa only [map_sum, minimalMapAny_elementary] using h

variable {A B H : Type*} [CStarAlgebra A] [CStarAlgebra B]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma hilbert_tensor_algebraic_bound (μ : A ⊗[ℂ] B →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hn : ∀ (n : ℕ) (a : Fin n → A) (b : Fin n → B),
      ‖∑ i, μ (a i ⊗ₜ[ℂ] b i)‖ ≤ ‖∑ i, minimalElementary (a i) (b i)‖)
    (z : A ⊗[ℂ] B) : ‖μ z‖ ≤ ‖minimalAlgebraicLinear z‖ := by
  apply algebraic_linear_norm_le μ.toLinearMap _ z
  intro n a b
  simpa only [map_sum, AlgHom.toLinearMap_apply, StarAlgHom.coe_toAlgHom] using hn n a b

@[irreducible] def hilbertMinimalTensorExtend (μ : A ⊗[ℂ] B →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hn : ∀ z, ‖μ z‖ ≤ ‖minimalAlgebraicLinear z‖) :
    MinimalTensor A B →⋆ₙₐ[ℂ] (H →L[ℂ] H) := minimalTensorExtend μ hn

lemma hilbertMinimalTensorExtend_elementary (μ : A ⊗[ℂ] B →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hn : ∀ z, ‖μ z‖ ≤ ‖minimalAlgebraicLinear z‖) (a : A) (b : B) :
    hilbertMinimalTensorExtend μ hn (minimalElementary a b) = μ (a ⊗ₜ[ℂ] b) := by
  unfold hilbertMinimalTensorExtend
  exact minimalTensorExtend_elementary μ hn a b

end WeakPureInfiniteness

end

end OAI
