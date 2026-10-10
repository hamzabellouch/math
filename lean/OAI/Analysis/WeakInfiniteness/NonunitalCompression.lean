import Mathlib
import OAI.Analysis.WeakInfiniteness.NonunitalColumn
import OAI.Analysis.WeakInfiniteness.NuclearCompression

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

open scoped CStarAlgebra ComplexOrder

universe u

section Central

variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {n : ℕ}

lemma finiteCompression_nonunital_commutator (v : Fin n → A) (φ : A →L[ℂ] CStarMatrix (Fin n) (Fin n) ℂ)
    (hφ : CompletelyPositive φ) (a r : A) :
    a*finiteCompression v r-finiteCompression v r*a=
      -(∑ i,star (nonunitalCoefficientAction (φ (star a)) v i-v i*star a)*r*v i)+
        ∑ i,star (v i)*r*(nonunitalCoefficientAction (φ a) v i-v i*a) := by
  have he : (∑ i,∑ j,φ a j i • (star (v j)*r*v i)) =
      ∑ i,∑ j,φ a i j • (star (v i)*r*v j) := Finset.sum_comm
  simp only [finiteCompression,nonunitalCoefficientAction,star_sub,star_sum,star_smul,
    completelyPositive_map_star hφ,CStarMatrix.star_apply,star_star,star_mul,
    Finset.sum_mul,Finset.mul_sum,sub_mul,mul_sub,Finset.sum_sub_distrib,
    smul_mul_assoc,mul_smul_comm]
  rw [he]
  simp only [mul_assoc]
  abel

lemma finiteCompression_nonunital_commutator_norm_le (v : Fin n → A)
    (φ : A →L[ℂ] CStarMatrix (Fin n) (Fin n) ℂ) (hφ : CompletelyPositive φ)
    (hv : ‖∑ i,star (v i)*v i‖≤1) (a r : A) (hr : ‖r‖≤1) :
    ‖a*finiteCompression v r-finiteCompression v r*a‖ ≤
      Real.sqrt ‖∑ i,star (nonunitalCoefficientAction (φ (star a)) v i-v i*star a)*
        (nonunitalCoefficientAction (φ (star a)) v i-v i*star a)‖+
      Real.sqrt ‖∑ i,star (nonunitalCoefficientAction (φ a) v i-v i*a)*
        (nonunitalCoefficientAction (φ a) v i-v i*a)‖ := by
  let d (a : A) (i : Fin n) := nonunitalCoefficientAction (φ a) v i-v i*a
  have hs : Real.sqrt ‖∑ i,star (v i)*v i‖≤1 := (Real.sqrt_le_one).mpr hv
  rw [finiteCompression_nonunital_commutator v φ hφ a r]
  calc
    _ ≤ ‖∑ i,star (d (star a) i)*r*v i‖+‖∑ i,star (v i)*r*d a i‖ := by
      simpa only [norm_neg] using norm_add_le
        (-(∑ i,star (d (star a) i)*r*v i)) (∑ i,star (v i)*r*d a i)
    _ ≤ (Real.sqrt ‖∑ i,star (d (star a) i)*d (star a) i‖*‖r‖*
        Real.sqrt ‖∑ i,star (v i)*v i‖)+
        (Real.sqrt ‖∑ i,star (v i)*v i‖*‖r‖*Real.sqrt ‖∑ i,star (d a i)*d a i‖) :=
      add_le_add (norm_finite_sandwich_le (d (star a)) v r)
        (norm_finite_sandwich_le v (d a) r)
    _ ≤ (Real.sqrt ‖∑ i,star (d (star a) i)*d (star a) i‖*1*1)+
        (1*1*Real.sqrt ‖∑ i,star (d a i)*d a i‖) := by gcongr
    _ = _ := by simp only [mul_one,one_mul,d]

end Central

end

end WeakPureInfiniteness
end

end OAI
