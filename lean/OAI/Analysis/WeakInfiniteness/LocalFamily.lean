import Mathlib
import OAI.Analysis.WeakInfiniteness.LocalPair

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

universe u v

variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {B : Type v} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

omit [PartialOrder A] [StarOrderedRing A] in
lemma mul_zero_of_mem_hereditary_left {a b x : A} (ha : IsSelfAdjoint a)
    (hab : a*b=0) (hx : x ∈ hereditarySubalgebra a ha) : x*b=0 := by
  apply closure_minimal _ (isClosed_eq (continuous_id.mul_const b) continuous_const) hx
  rintro _ ⟨c,rfl⟩
  change a*c*a*b=0
  rw [mul_assoc,hab,mul_zero]

omit [PartialOrder A] [StarOrderedRing A] in
lemma mul_zero_of_hereditary {a b x y : A} (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b)
    (hab : a*b=0) (hx : x ∈ hereditarySubalgebra a ha) (hy : y ∈ hereditarySubalgebra b hb) :
    x*y=0 := by
  have hxb := mul_zero_of_mem_hereditary_left ha hab hx
  apply closure_minimal _ (isClosed_eq (continuous_const.mul continuous_id) continuous_const) hy
  rintro _ ⟨c,rfl⟩
  change x*(b*c*b)=0
  rw [← mul_assoc,← mul_assoc,hxb,zero_mul,zero_mul]

lemma exists_orthogonal_detected_family {n : ℕ} (hn : 1 ≤ n)
    (hpi : ∀ a : A,0 ≤ a → a ≠ 0 → ProperlyInfinite (diagonalCopies n a))
    (π : A →⋆ₙₐ[ℂ] B) (m : ℕ) {h : A} (hh : 0 ≤ h) (hhn : π h ≠ 0) :
    ∃ x : Fin m → A,
      (∀ i,x i ∈ hereditarySubalgebra h hh.isSelfAdjoint ∧ 0 ≤ x i ∧ π (x i) ≠ 0) ∧
      ∀ i j,i ≠ j → x i*x j=0 := by
  induction m generalizing h with
  | zero => exact ⟨Fin.elim0,by simp⟩
  | succ m ih =>
    obtain ⟨a,ha,b,hb,ha0,hb0,hab,han,hbn⟩ := exists_orthogonal_detected_pair hn hpi π hh hhn
    obtain ⟨x,hx,hxx⟩ := ih ha0 han
    refine ⟨Fin.cons b x,?_,?_⟩
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact ⟨hb,hb0,hbn⟩
      · exact ⟨hereditarySubalgebra_le_of_mem (hereditarySubalgebra_inner h hh.isSelfAdjoint)
          ha0.isSelfAdjoint ha (hx j).1,(hx j).2⟩
    · intro i j
      refine Fin.cases ?_ (fun i => ?_) i
      · refine Fin.cases (by simp) (fun j _ => ?_) j
        have he := mul_zero_of_mem_hereditary_left ha0.isSelfAdjoint hab (hx j).1
        have he' := congrArg star he
        simpa only [Fin.cons_zero,Fin.cons_succ,star_mul,hb0.star_eq,(hx j).2.1.star_eq,star_zero] using he'
      · refine Fin.cases (fun _ => ?_) (fun j hij => ?_) j
        · exact mul_zero_of_mem_hereditary_left ha0.isSelfAdjoint hab (hx i).1
        · exact hxx i j (fun he => hij (congrArg Fin.succ he))

end

end WeakPureInfiniteness
end

end OAI
