import OAI.Analysis.Pureness.Tensor.SpatialExpectationFaithful
import OAI.Analysis.Pureness.Tensor.SpatialTensorContinuousLegs

namespace OAI
noncomputable section
namespace CuntzPureness
open scoped TensorProduct
variable {A H G E : Type*} [Group G] [CStarAlgebra A] [CStarAlgebra E]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (α : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (hα : Function.Injective α)

def spatialCoefficientExpectation :
    representedSpatialTensor α (reducedGroupAlgebra G).subtype →L[ℂ]
      representedSpatialTensor α (reducedGroupAlgebra G).subtype :=
  (spatialTensorLeftLeg α (reducedGroupAlgebra G).subtype 1).comp
    (spatialGroupFourier α (1 : G))

include hα in
lemma spatialGroupFourier_left (a : A) :
    spatialGroupFourier α (1 : G)
      (spatialCompletionMap α (reducedGroupAlgebra G).subtype (a ⊗ₜ[ℂ] 1)) = a := by
  simpa using spatialGroupFourier_generator α hα (1 : G) 1 a

include hα in
lemma spatialCoefficientExpectation_left (a : A) :
    spatialCoefficientExpectation (G := G) α
      (spatialCompletionMap α (reducedGroupAlgebra G).subtype (a ⊗ₜ[ℂ] 1)) =
      spatialCompletionMap α (reducedGroupAlgebra G).subtype (a ⊗ₜ[ℂ] 1) := by
  exact congrArg (spatialTensorLeftLeg α (reducedGroupAlgebra G).subtype 1)
    (spatialGroupFourier_left α hα a)

include hα in
lemma spatialCoefficientExpectation_idempotent
    (x : representedSpatialTensor α (reducedGroupAlgebra G).subtype) :
    spatialCoefficientExpectation (G := G) α (spatialCoefficientExpectation (G := G) α x) =
      spatialCoefficientExpectation (G := G) α x :=
  spatialCoefficientExpectation_left α hα _

include hα in
lemma spatialCoefficientExpectation_square_eq_zero_iff
    (x : representedSpatialTensor α (reducedGroupAlgebra G).subtype) :
    spatialCoefficientExpectation (G := G) α (star x*x) = 0 ↔ x = 0 := by
  constructor
  · intro hx
    apply (spatialGroupFourier_square_eq_zero_iff α hα x).mp
    have h := congrArg (spatialGroupFourier α (1 : G)) hx
    change spatialGroupFourier α (1 : G)
      (spatialCompletionMap α (reducedGroupAlgebra G).subtype
        (spatialGroupFourier α (1 : G) (star x*x) ⊗ₜ[ℂ] 1)) = _ at h
    simpa only [spatialGroupFourier_left α hα, map_zero] using h
  · rintro rfl
    simp

include hα in

theorem spatialHom_injective_of_expectation_kernel
    (Φ : representedSpatialTensor α (reducedGroupAlgebra G).subtype →⋆ₐ[ℂ] E)
    (hl : Function.Injective (fun a : A =>
      Φ (spatialCompletionMap α (reducedGroupAlgebra G).subtype (a ⊗ₜ[ℂ] 1))))
    (hk : ∀ x, Φ x = 0 → Φ (spatialCoefficientExpectation (G := G) α x) = 0) :
    Function.Injective Φ := by
  have hz (x : representedSpatialTensor α (reducedGroupAlgebra G).subtype) (hx : Φ x = 0) :
      x = 0 := by
    apply (spatialGroupFourier_square_eq_zero_iff α hα x).mp
    have hs : Φ (star x*x) = 0 :=
      (map_mul Φ (star x) x).trans
        ((congrArg (fun z => Φ (star x) * z) hx).trans (mul_zero _))
    have ht := hk (star x*x) hs
    have hzero : Φ ((spatialTensorLeftLeg α (reducedGroupAlgebra G).subtype 1) 0) = 0 :=
      (congrArg Φ (map_zero (spatialTensorLeftLeg α (reducedGroupAlgebra G).subtype 1))).trans
        (map_zero Φ)
    exact hl (ht.trans hzero.symm)

  intro x y hxy
  exact sub_eq_zero.mp (hz (x-y) ((map_sub Φ x y).trans (sub_eq_zero.mpr hxy)))
end CuntzPureness

end

end OAI
