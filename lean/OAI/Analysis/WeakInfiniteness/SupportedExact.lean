import Mathlib
import OAI.Analysis.WeakInfiniteness.SupportedCorner
import OAI.Analysis.WeakInfiniteness.UnitizationExact

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

universe u

noncomputable section

variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {n : ℕ}

omit [PartialOrder A] [StarOrderedRing A] in
instance supportedAlgebra_isClosed (e : A) (he : IsSelfAdjoint e) :
    IsClosed (supportedAlgebra e he : Set A) := supportedAlgebra_closed e he

lemma exact_supportedAlgebra (hA : Exact A) (U : CStarMatrix (Fin 1) (Fin n) A)
    (e : CStarMatrix (Fin n) (Fin n) A) (he : IsSelfAdjoint e) (hU : U.conjTranspose*U=e) :
    Exact (supportedAlgebra e he) :=
  exact_subalgebra (matrixSingletonHom.comp (supportedCompression U e he hU))
    (matrixSingletonHom_injective.comp (supportedCompression_injective U e he hU)) hA

lemma exact_unitization_supportedAlgebra (hA : Exact A) (U : CStarMatrix (Fin 1) (Fin n) A)
    (e : CStarMatrix (Fin n) (Fin n) A) (he : IsSelfAdjoint e) (hU : U.conjTranspose*U=e) :
    Exact (Unitization ℂ (supportedAlgebra e he)) :=
  exact_unitization (exact_supportedAlgebra hA U e he hU)

end

end WeakPureInfiniteness
end

end OAI
