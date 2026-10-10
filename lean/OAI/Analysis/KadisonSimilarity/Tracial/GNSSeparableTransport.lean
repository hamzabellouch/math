import OAI.Analysis.KadisonSimilarity.Tracial.PredualGNSSeparable

namespace OAI

/-! Separability follows a trace-preserving equivalence of the actual algebras. -/

noncomputable section
namespace KadisonSimilarity
open Generator.Tracial
open scoped ComplexOrder

variable {A B : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  (τA : A →ₚ[ℂ] ℂ) (τB : B →ₚ[ℂ] ℂ)
  (e : A ≃⋆ₐ[ℂ] B) (ht : ∀ a, τB (e a) = τA a)

include ht in
theorem gns_separable_of_trace_equiv [TopologicalSpace.SeparableSpace τA.GNS] :
    TopologicalSpace.SeparableSpace τB.GNS := by
  let J := gnsTracialHomIsometry τA τB e.toStarAlgHom ht
  have hJ : Function.Surjective J := by
    intro x
    change x ∈ Set.range J
    refine (gnsTracialVector_dense τB).induction_on x
      J.isometry.isClosedEmbedding.isClosed_range ?_
    intro b
    obtain ⟨a, rfl⟩ := e.surjective b
    exact ⟨gnsTracialVector τA a, gnsTracialHomIsometry_vector τA τB e.toStarAlgHom ht a⟩
  have hs := TopologicalSpace.isSeparable_range J.continuous
  rw [Set.range_eq_univ.mpr hJ] at hs
  exact TopologicalSpace.isSeparable_univ_iff.mp hs

end KadisonSimilarity

end

end OAI
