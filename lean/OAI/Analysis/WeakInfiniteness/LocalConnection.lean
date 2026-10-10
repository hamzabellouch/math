import Mathlib
import OAI.Analysis.WeakInfiniteness.PerturbationRows

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

open scoped CStarAlgebra Topology

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

abbrev ElementCuntzSubequiv (a b : A) : Prop :=
  CuntzSubequiv (diagonalCopies 1 a) (diagonalCopies 1 b)

lemma elementCuntzSubequiv_iff {a b : A} : ElementCuntzSubequiv a b ↔
    ∀ ε : ℝ,0 < ε → ∃ v : A,‖star v*b*v-a‖ < ε := by
  constructor
  · intro hab ε hε
    obtain ⟨v,hv⟩ := hab ε hε
    refine ⟨matrixSingletonHom v,?_⟩
    have he := NonUnitalStarAlgHom.norm_apply_le (matrixSingletonHom (A := A))
      (star v*diagonalCopies 1 b*v-diagonalCopies 1 a)
    simp only [map_sub,map_mul,map_star,singleton_diagonal] at he
    exact he.trans_lt hv
  · intro hab ε hε
    obtain ⟨v,hv⟩ := hab ε hε
    refine ⟨diagonalCopies 1 v,?_⟩
    have he := NonUnitalStarAlgHom.norm_apply_le (diagonalHom (A := A) 1) (star v*b*v-a)
    simp only [map_sub,map_mul,map_star,CStarMatrix.star_eq_conjTranspose] at he
    exact he.trans_lt hv

lemma elementCuntzSubequiv_of_hereditary {a b : A} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hm : a ∈ hereditarySubalgebra b hb.isSelfAdjoint) : ElementCuntzSubequiv a b :=
  elementCuntzSubequiv_iff.mpr (exists_comparison_of_hereditary b a hb ha hm)

lemma element_initial_cuntz_range (z : A) : ElementCuntzSubequiv (star z*z) (z*star z) :=
  elementCuntzSubequiv_iff.mpr (exists_comparison_of_star_mul z)

lemma element_range_cuntz_initial (z : A) : ElementCuntzSubequiv (z*star z) (star z*z) := by
  simpa only [star_star] using element_initial_cuntz_range (star z)

end

end WeakPureInfiniteness
end

end OAI
