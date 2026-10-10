import Mathlib
import OAI.Analysis.WeakInfiniteness.ReducedOperators
import OAI.Analysis.WeakInfiniteness.SmallCStar

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

instance fullGroup_separable {G : Type*} [Group G] [Countable G] :
    SeparableSpace (FullGroupAlgebra G) := by
  have hs : IsSeparable (fullGroupSubalgebra G : Set (FullGroupAmbient G)) := by
    rw [fullGroupSubalgebra_eq_closure_span]
    exact (Set.countable_range (fullGroupOperator (G := G))).isSeparable.span.closure
  exact hs.separableSpace

instance fullGroup_small {G : Type*} [Group G] [Countable G] : Small.{0} (FullGroupAlgebra G) :=
  small_of_separable_metric _

instance reducedFreeLarge_separable : SeparableSpace ReducedFreeLarge := by
  have hs := isSeparable_range (starHom_continuous fullToReducedLarge)
  rw [Set.range_eq_univ.mpr fullToReducedLarge_surjective] at hs
  exact isSeparable_univ_iff.mp hs

instance reducedFreeLarge_small : Small.{0} ReducedFreeLarge := small_of_separable_metric _

end

end WeakPureInfiniteness
end

end OAI
