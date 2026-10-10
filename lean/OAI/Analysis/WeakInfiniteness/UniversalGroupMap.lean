import Mathlib
import OAI.Analysis.WeakInfiniteness.PairUnitary
import OAI.Analysis.WeakInfiniteness.UniversalFreeEmbedding

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

namespace WeakPureInfiniteness

def pairRepresentation (π : ContractionRepresentation) : GroupRepresentation (FreeGroup Bool) where
  hilbert := π.hilbert
  group := pairGroup π.operator

def pairAmbientMap : FullGroupAmbient (FreeGroup Bool) →⋆ₐ[ℂ] ContractionAmbient where
  toFun x := ⟨fun π => x (pairRepresentation π), memℓp_infty ⟨‖x‖, by
    rintro _ ⟨π,rfl⟩
    exact lp.norm_apply_le_norm ENNReal.top_ne_zero x (pairRepresentation π)⟩⟩
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_one' := rfl
  commutes' _ := rfl
  map_star' _ := rfl

lemma pairAmbientMap_element (g : FreeGroup Bool) :
    pairAmbientMap (fullGroupOperator g) =
      ((pairGroup universalContractionGenerator g : UniversalContraction).val) := by
  apply Subtype.ext
  funext π
  exact (map_pairGroup (contractionEvaluation π) universalContractionGenerator g).symm

lemma pairAmbientMap_mem (x : FullGroupAlgebra (FreeGroup Bool)) :
    pairAmbientMap x.val ∈ universalContractionSubalgebra := by
  have hcont : Continuous pairAmbientMap :=
    (pairAmbientMap.toAlgHom.toLinearMap.mkContinuous 1 (fun x => by
      change ‖pairAmbientMap x‖ ≤ 1 * ‖x‖
      rw [one_mul]
      exact NonUnitalStarAlgHom.norm_apply_le pairAmbientMap x)).continuous
  have hs : fullGroupSubalgebra (FreeGroup Bool) ≤
      universalContractionSubalgebra.comap pairAmbientMap := by
    apply closedStarSpan_le
    · exact (closedStarSpan_closed _).preimage hcont
    · rintro _ ⟨g,rfl⟩
      change pairAmbientMap (fullGroupOperator g) ∈ universalContractionSubalgebra
      rw [pairAmbientMap_element]
      exact (pairGroup universalContractionGenerator g : UniversalContraction).property
  exact hs x.property

def fullToUniversal : FullGroupAlgebra (FreeGroup Bool) →⋆ₐ[ℂ] UniversalContraction :=
  (pairAmbientMap.comp (fullGroupSubalgebra (FreeGroup Bool)).subtype).codRestrict
    universalContractionSubalgebra pairAmbientMap_mem

@[simp] lemma fullToUniversal_element (g : FreeGroup Bool) :
    fullToUniversal (fullGroupElement g) =
      (pairGroup universalContractionGenerator g : UniversalContraction) :=
  Subtype.ext (pairAmbientMap_element g)

lemma fullToUniversal_evaluation (π : ContractionRepresentation)
    (x : FullGroupAlgebra (FreeGroup Bool)) :
    contractionEvaluation π (fullToUniversal x) = fullGroupEvaluation (pairRepresentation π) x := rfl

end WeakPureInfiniteness
end

end OAI
