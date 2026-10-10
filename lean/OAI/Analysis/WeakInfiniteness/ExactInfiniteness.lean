import Mathlib
import OAI.Analysis.WeakInfiniteness.StrongInfiniteness

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

theorem exact_weaklyPurelyInfinite_stronglyPurelyInfinite
    (A : Type u) [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (hExact : Exact A) (hWeak : WeaklyPurelyInfinite A) : StronglyPurelyInfinite A :=
  exact_weaklyPurelyInfinite_stronglyPurelyInfinite_any hExact hWeak

end WeakPureInfiniteness
end

end OAI
