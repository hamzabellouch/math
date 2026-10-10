import Mathlib

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped InnerProductSpace

variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

lemma exists_reducing_column (L : E →L[ℂ] F) (T : G →ₗᵢ[ℂ] E)
    (D : G →L[ℂ] G) (a : E →L[ℂ] E)
    (hL : L.adjoint.comp (L.comp T.toContinuousLinearMap) = T.toContinuousLinearMap)
    (ha : a.comp T.toContinuousLinearMap = T.toContinuousLinearMap.comp D)
    (ha' : a.adjoint.comp T.toContinuousLinearMap = T.toContinuousLinearMap.comp D.adjoint) :
    ∃ J : G →ₗᵢ[ℂ] F,
      J.toContinuousLinearMap=L.comp T.toContinuousLinearMap ∧
      (L.comp (a.comp L.adjoint)).comp J.toContinuousLinearMap=J.toContinuousLinearMap.comp D ∧
      (L.comp (a.comp L.adjoint)).adjoint.comp J.toContinuousLinearMap=J.toContinuousLinearMap.comp D.adjoint := by
  have hpoint (x : G) : L.adjoint (L (T x))=T x := congrArg (fun t : G →L[ℂ] E => t x) hL
  let J₀ := L.toLinearMap.comp T.toLinearMap
  have hi : ∀ x y, inner ℂ (J₀ x) (J₀ y)=inner ℂ x y := by
    intro x y
    change inner ℂ (L (T x)) (L (T y))=inner ℂ x y
    rw [← ContinuousLinearMap.adjoint_inner_right, hpoint]
    exact T.inner_map_map x y
  let J := J₀.isometryOfInner hi
  have hJ : J.toContinuousLinearMap=L.comp T.toContinuousLinearMap := by ext x; rfl
  refine ⟨J,hJ,?_,?_⟩
  · rw [hJ]
    ext x
    change L (a (L.adjoint (L (T x))))=L (T (D x))
    rw [hpoint]
    exact congrArg L (congrArg (fun t : G →L[ℂ] E => t x) ha)
  · rw [hJ]
    simp only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint]
    ext x
    change L (a.adjoint (L.adjoint (L (T x))))=L (T (D.adjoint x))
    rw [hpoint]
    exact congrArg L (congrArg (fun t : G →L[ℂ] E => t x) ha')

end

end WeakPureInfiniteness
end

end OAI
