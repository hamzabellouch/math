import OAI.Analysis.WeakInfiniteness.CrossUniverseTensorLaws

namespace OAI

/-! Surjective factor maps induce a surjective minimal tensor map. -/

noncomputable section

namespace WeakPureInfiniteness

variable {A B C D : Type*}
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [NonUnitalCStarAlgebra C] [NonUnitalCStarAlgebra D]

theorem minimalMapAny_surjective (φ : A →⋆ₙₐ[ℂ] B) (ψ : C →⋆ₙₐ[ℂ] D)
    (hφ : Function.Surjective φ) (hψ : Function.Surjective ψ) :
    Function.Surjective (minimalMapAny φ ψ) := by
  let q := minimalMapAny φ ψ
  let S : Submodule ℂ (MinimalTensor B D) := (q : MinimalTensor A C →ₗ[ℂ] _).range
  have hS : S = ⊤ := by
    apply minimal_elementary_span_dense S (nonUnitalStarHom_isClosed_range q)
    intro b d
    obtain ⟨a, rfl⟩ := hφ b
    obtain ⟨c, rfl⟩ := hψ d
    exact ⟨minimalElementary a c, minimalMapAny_elementary φ ψ a c⟩
  intro y
  have hy : y ∈ S := by rw [hS]; trivial
  exact hy

end WeakPureInfiniteness

end

end OAI
