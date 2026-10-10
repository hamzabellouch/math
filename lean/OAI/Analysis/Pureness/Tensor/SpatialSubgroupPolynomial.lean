import OAI.Analysis.Pureness.Tensor.SpatialGroupPolynomialMap
import OAI.Analysis.Pureness.Tensor.SpatialGroupMatrixSlices
import OAI.Analysis.Pureness.Tensor.SpatialSliceCompression
import OAI.Analysis.Pureness.Tensor.SpatialSchurNorm
import OAI.Analysis.Pureness.GroupAlgebra.SubgroupCosetKernel

namespace OAI
noncomputable section
namespace CuntzPureness
open scoped Classical
local instance spatialSubgroupPolynomialDecidableEq {X : Type*} : DecidableEq X := Classical.decEq X
open scoped TensorProduct InnerProductSpace
variable {A H G : Type*} [Group G] [CStarAlgebra A]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (α : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (hα : Function.Injective α)

def groupPolynomialMask (U : Subgroup G) : (G →₀ A) →ₗ[ℂ] (G →₀ A) where
  toFun := Finsupp.filter (fun g => g ∈ U)
  map_add' _ _ := Finsupp.filter_add
  map_smul' _ _ := Finsupp.filter_smul

include hα in
lemma spatialGroupPolynomialMap_compression (a : G →₀ A) (g h : G) :
    α (a (g*h⁻¹)) =
      (spatialRightVector (H := H) (lp.single 2 g (1 : ℂ))).adjoint.comp
        ((spatialGroupPolynomialMap (G := G) α a).val.comp
          (spatialRightVector (lp.single 2 h (1 : ℂ)))) :=
  (congrArg α (spatialGroupPolynomialMap_fourier α hα a (g*h⁻¹))).symm.trans
    ((congrArg α (spatialGroupMatrixSlice_eq_fourier α hα g h
      (spatialGroupPolynomialMap (G := G) α a))).symm.trans
        (spatialVectorSlice_compression α hα (reducedGroupAlgebra G).subtype
          (lp.single 2 g 1) (lp.single 2 h 1) (spatialGroupPolynomialMap (G := G) α a)))

include hα in

theorem spatialGroupPolynomialMask_norm_le (U : Subgroup G) (a : G →₀ A) :
    ‖spatialGroupPolynomialMap (G := G) α (groupPolynomialMask U a)‖ ≤
      ‖spatialGroupPolynomialMap (G := G) α a‖ := by
  apply spatialSchur_norm_le (subgroupCosetVector U) (subgroupCosetVector U)
    (fun g => (subgroupCosetVector_norm U g).le) (fun g => (subgroupCosetVector_norm U g).le)
    (spatialGroupPolynomialMap (G := G) α (groupPolynomialMask U a)).val
    (spatialGroupPolynomialMap (G := G) α a).val
  intro g h
  refine (spatialGroupPolynomialMap_compression α hα (groupPolynomialMask U a) g h).symm.trans ?_
  have hm : α ((groupPolynomialMask U a) (g*h⁻¹)) =
      (if g*h⁻¹ ∈ U then (1 : ℂ) else 0) •
        ((spatialRightVector (H := H) (lp.single 2 g (1 : ℂ))).adjoint.comp
          ((spatialGroupPolynomialMap (G := G) α a).val.comp
            (spatialRightVector (lp.single 2 h (1 : ℂ))))) := by
    change α (if g*h⁻¹ ∈ U then a (g*h⁻¹) else 0) = _
    by_cases hm : g*h⁻¹ ∈ U
    · simp only [ite_eq_left hm, one_smul]
      exact spatialGroupPolynomialMap_compression α hα a g h
    · simp only [ite_eq_right hm, map_zero, zero_smul]
  exact hm.trans (congrArg (fun c : ℂ => c •
    ((spatialRightVector (H := H) (lp.single 2 g (1 : ℂ))).adjoint.comp
      ((spatialGroupPolynomialMap (G := G) α a).val.comp
        (spatialRightVector (lp.single 2 h (1 : ℂ)))))) (subgroupCosetVector_inner U g h).symm)
end CuntzPureness

end

end OAI
