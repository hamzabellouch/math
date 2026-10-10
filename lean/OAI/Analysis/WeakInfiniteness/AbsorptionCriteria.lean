import Mathlib
import OAI.Analysis.WeakInfiniteness.CentralExactPair
import OAI.Analysis.WeakInfiniteness.CentralOInfinityCopies
import OAI.Analysis.WeakInfiniteness.HalfFlipCriterion

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

def oInfinityAbsorptionEquiv_of_contractiveDiagonalization
    (A : Type u) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [SeparableSpace A] (h : ContractiveIdentityDiagonalization A)
    (hflip : ApproximateHalfFlip OInfinity) :
    A ≃⋆ₐ[ℂ] MinimalTensor A OInfinity :=
  oInfinityAbsorptionEquiv_of_elementaryIntertwining A
    (elementaryUnitaryIntertwining_of_centralCopies_halfFlip
      h.centralExactCuntzPair.approximatelyCentralCopies hflip)

lemma oInfinity_no_character (φ : OInfinity →⋆ₐ[ℂ] ℂ) : False := by
  let r := φ (oInfinityIsometry 0)
  let s := φ (oInfinityIsometry 1)
  have hr : star r*r=1 := by
    dsimp only [r]
    rw [← map_star,← map_mul,oInfinityIsometry_relations,ite_eq_left rfl,map_one]
  have hs : star s*s=1 := by
    dsimp only [s]
    rw [← map_star,← map_mul,oInfinityIsometry_relations,ite_eq_left rfl,map_one]
  have hrs : star r*s=0 := by
    dsimp only [r,s]
    rw [← map_star,← map_mul,oInfinityIsometry_relations,ite_eq_right (by omega),map_zero]
  rcases mul_eq_zero.mp hrs with h | h
  · rw [h,zero_mul] at hr
    exact zero_ne_one hr
  · rw [h,mul_zero] at hs
    exact zero_ne_one hs

lemma oInfinity_no_unital_map_into_forcedUnitization
    (A : Type u) [NonUnitalCStarAlgebra A]
    (φ : OInfinity →⋆ₐ[ℂ] Unitization ℂ A) : False := by
  let χ : Unitization ℂ A →⋆ₐ[ℂ] ℂ :=
    { Unitization.fstHom ℂ A with map_star' := Unitization.fst_star }
  exact oInfinity_no_character (χ.comp φ)

end

end WeakPureInfiniteness
end

end OAI
