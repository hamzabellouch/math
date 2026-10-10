import Mathlib
import OAI.Analysis.WeakInfiniteness.ExactHereditary
import OAI.Analysis.WeakInfiniteness.NormKernelWitness
import OAI.Analysis.WeakInfiniteness.ProductRepresentation
import OAI.Analysis.WeakInfiniteness.UniversalGroupEmbedding

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

def universalHilbert : ComplexHilbert.{1} where
  Carrier := lp (fun π : ContractionRepresentation => π.hilbert) 2

def contractionAmbientRepresentation :
    ContractionAmbient →⋆ₙₐ[ℂ] (universalHilbert →L[ℂ] universalHilbert) :=
  productRepresentation

lemma contractionAmbientRepresentation_injective :
    Function.Injective contractionAmbientRepresentation := productRepresentation_injective

def universalFaithfulRepresentation :
    UniversalContraction →⋆ₙₐ[ℂ] (universalHilbert →L[ℂ] universalHilbert) :=
  contractionAmbientRepresentation.comp
    universalContractionSubalgebra.subtype.toNonUnitalStarAlgHom

lemma universalFaithfulRepresentation_injective :
    Function.Injective universalFaithfulRepresentation :=
  contractionAmbientRepresentation_injective.comp Subtype.val_injective

theorem universalContraction_not_exact : ¬ Exact UniversalContraction := by
  intro h
  exact fullFreeTwo_not_exact
    (exact_of_injective_unital fullToUniversal fullToUniversal_injective
      universalHilbert universalFaithfulRepresentation universalFaithfulRepresentation_injective h)

end WeakPureInfiniteness
end

end OAI
