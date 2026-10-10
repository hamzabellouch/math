import Mathlib
import OAI.Analysis.WeakInfiniteness.IntertwiningEquiv
import OAI.Analysis.WeakInfiniteness.TensorAbsorption
import OAI.Analysis.WeakInfiniteness.OInfinityUniversal

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

open TopologicalSpace

universe u

def oInfinityAbsorptionEquiv_of_finiteIntertwining
    (A : Type u) [NonUnitalCStarAlgebra A] [SeparableSpace A]
    (h : FiniteIntertwining (minimalLeftEmbedding A OInfinity)) :
    A ≃⋆ₐ[ℂ] MinimalTensor A OInfinity :=
  finiteIntertwiningStarEquiv (minimalLeftEmbedding A OInfinity)
    (minimalLeftEmbedding_isometry A OInfinity) h

end

end WeakPureInfiniteness
end

end OAI
