import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.TensorProducts.CommutingStarTensor

namespace OAI


noncomputable section
namespace ActualSpatial
open Pureness UnitalTomsWinter
open scoped CStarAlgebra TensorProduct InnerProductSpace

variable (A D : Type*) [CStarAlgebra A] [CStarAlgebra D]
variable [PartialOrder A] [StarOrderedRing A] [PartialOrder D] [StarOrderedRing D]

abbrev tensorMap : A ⊗[ℂ] D →⋆ₐ[ℂ] Tensor A D :=
  commutingTensorClosureMap (N := Op A D) (leftAction A D) (rightAction A D) (commute A D)

lemma tensorMap_tmul (a : A) (d : D) : tensorMap A D (a ⊗ₜ[ℂ] d)=leftHom A D a*rightHom A D d := rfl
lemma tensorMap_dense : DenseRange (tensorMap A D) := commutingTensorClosureMap_denseRange _ _ _
lemma tensorMap_injective : Function.Injective (tensorMap A D) := by
  intro z w h
  exact spatialStarTensorHom_injective_of_faithful (repA A) (repA D)
    (stateHilbertRepresentation_injective A) (stateHilbertRepresentation_injective D)
    (congrArg Subtype.val h)
lemma leftHom_injective [Nontrivial D] : Function.Injective (leftHom A D) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro a ha
  have he : tensorMap A D (a ⊗ₜ[ℂ] (1 : D))=tensorMap A D 0 := by
    simpa only [tensorMap_tmul,map_one,mul_one,map_zero] using ha
  have hz := congrArg (TensorProduct.comm ℂ A D) (tensorMap_injective A D he)
  simpa only [TensorProduct.comm_tmul,map_zero,Module.FaithfullyFlat.one_tmul_eq_zero_iff] using hz

end ActualSpatial

end

end OAI
