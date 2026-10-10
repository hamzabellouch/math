import OAI.Analysis.Nuclearity.FactorTensorExtension
import OAI.Analysis.Nuclearity.MinimalTensorAlgebraic

namespace OAI

/-! The spatial description of the represented factor product. Nuclearity
of the actual represented left image is explicitly required. -/

noncomputable section
open scoped TensorProduct
open KirchbergRordam.GenericRW

namespace WeakPureInfiniteness

section Generic

attribute [local instance] UnitalMinimalTensor.algebraicTensorUnital

universe u v w
variable {C : Type u} {D : Type v} {H : Type w} [CStarAlgebra C] [CStarAlgebra D]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem exists_minimal_factor_tensor_extension (hC : Pureness.IsNuclear.{u,v} C)
    (M : VonNeumannAlgebra H) (hM : FactorIndependence.IsFactor M)
    (φ : C →⋆ₐ[ℂ] (H →L[ℂ] H)) (ψ : D →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hφ : Function.Injective φ) (hψ : Function.Injective ψ)
    (hφM : ∀ c, φ c ∈ M) (hψM : ∀ d, ψ d ∈ M.commutant)
    (hc : ∀ c d, Commute (φ c) (ψ d)) :
    ∃ θ : MinimalTensor C D →⋆ₙₐ[ℂ] (H →L[ℂ] H),
      Isometry θ ∧ ∀ c d, θ (minimalElementary c d) = φ c * ψ d := by
  let f : C ⊗[ℂ] D →⋆ₐ[ℂ] MinimalTensor C D :=
    UnitalMinimalTensor.algebraicMap (A := C) (B := D)
  have hf : Function.Injective f :=
    UnitalMinimalTensor.algebraicMap_injective (A := C) (B := D)
  have hd : DenseRange f :=
    UnitalMinimalTensor.algebraicMap_dense (A := C) (B := D)
  obtain ⟨θ, hθ, he⟩ := exists_factor_tensor_extension (A := C) (B := D) (E := MinimalTensor C D) hC f hf hd
    M hM φ ψ hφ hψ hφM hψM hc
  refine ⟨θ.toNonUnitalStarAlgHom, hθ, ?_⟩
  intro c d
  change θ (minimalElementary c d) = _
  simpa only [f, UnitalMinimalTensor.algebraicMap_tmul,
    Pureness.commutingStarTensorHom_tmul] using he (c ⊗ₜ[ℂ] d)

end Generic

end WeakPureInfiniteness

end

end OAI
