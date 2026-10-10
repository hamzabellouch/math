import OAI.Analysis.Pureness.Tensor.SpatialFourierCoefficients
import OAI.Analysis.Pureness.Tensor.SpatialGroupPolynomialDensity
import Mathlib.LinearAlgebra.Finsupp.LSum

namespace OAI
noncomputable section
namespace CuntzPureness
local instance spatialGroupPolynomialMapDecidableEq {X : Type*} :
    DecidableEq X := Classical.decEq X
open scoped TensorProduct
variable {A H G : Type*} [Group G] [CStarAlgebra A]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (α : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (hα : Function.Injective α)

def spatialGroupPolynomialMap : (G →₀ A) →ₗ[ℂ]
    representedSpatialTensor α (reducedGroupAlgebra G).subtype :=
  Finsupp.lsum ℂ (fun g => (spatialTensorLeftLeg α (reducedGroupAlgebra G).subtype
    (reducedGroupUnitary G g : reducedGroupAlgebra G)).toLinearMap)

lemma spatialGroupPolynomialMap_apply (a : G →₀ A) :
    spatialGroupPolynomialMap (G := G) α a = ∑ g ∈ a.support,
      spatialCompletionMap α (reducedGroupAlgebra G).subtype
        (a g ⊗ₜ[ℂ] (reducedGroupUnitary G g : reducedGroupAlgebra G)) := rfl

lemma spatialGroupPolynomialMap_single (g : G) (a : A) :
    spatialGroupPolynomialMap (G := G) α (Finsupp.single g a) =
      spatialCompletionMap α (reducedGroupAlgebra G).subtype
        (a ⊗ₜ[ℂ] (reducedGroupUnitary G g : reducedGroupAlgebra G)) := by
  exact Finsupp.lsum_single ℂ _ g a

lemma spatialGroupPolynomialMap_range :
    LinearMap.range (spatialGroupPolynomialMap (G := G) α) = spatialGroupPolynomial (G := G) α := by
  apply le_antisymm
  · rintro _ ⟨a, rfl⟩
    change (∑ g ∈ a.support, spatialCompletionMap α (reducedGroupAlgebra G).subtype
      (a g ⊗ₜ[ℂ] (reducedGroupUnitary G g : reducedGroupAlgebra G))) ∈
        spatialGroupPolynomial (G := G) α
    apply Submodule.sum_mem
    intro g hg
    exact spatialGroupPolynomial_generator α (a g) g
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨a,g⟩, rfl⟩
    exact ⟨Finsupp.single g a, spatialGroupPolynomialMap_single α g a⟩

lemma spatialGroupPolynomialMap_denseRange : DenseRange (spatialGroupPolynomialMap (G := G) α) := by
  have hr : Set.range (spatialGroupPolynomialMap (G := G) α) =
      (spatialGroupPolynomial (G := G) α :
        Set (representedSpatialTensor α (reducedGroupAlgebra G).subtype)) :=
    congrArg SetLike.coe (spatialGroupPolynomialMap_range (G := G) α)
  change Dense (Set.range (spatialGroupPolynomialMap (G := G) α))
  rw [hr]
  exact spatialGroupPolynomial_dense (G := G) α

include hα in
lemma spatialGroupPolynomialMap_fourier (a : G →₀ A) (g : G) :
    spatialGroupFourier α g (spatialGroupPolynomialMap (G := G) α a) = a g := by
  have he := spatialGroupFourier_polynomial α hα g a.support a
  change spatialGroupFourier α g (spatialGroupPolynomialMap (G := G) α a) = _ at he
  refine he.trans ?_
  by_cases hg : g ∈ a.support
  · exact ite_eq_left hg
  · simpa only [ite_eq_right hg] using (Finsupp.notMem_support_iff.mp hg).symm
end CuntzPureness

end

end OAI
