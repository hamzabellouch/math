import Mathlib
import OAI.Analysis.WeakInfiniteness.CPSchwarz

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

universe u v

section Range

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma cuntzPair_range_sum_le_one (r s : A)
    (hr : star r*r=1) (hs : star s*s=1) (hrs : star r*s=0) :
    r*star r+s*star s≤1 := by
  let p := r*star r
  let q := s*star s
  have hp : star p=p := by simp [p]
  have hq : star q=q := by simp [q]
  have hpp : p*p=p := by
    dsimp only [p]
    calc
      _ = r*(star r*r)*star r := by noncomm_ring
      _ = _ := by rw [hr,mul_one]
  have hqq : q*q=q := by
    dsimp only [q]
    calc
      _ = s*(star s*s)*star s := by noncomm_ring
      _ = _ := by rw [hs,mul_one]
  have hpq : p*q=0 := by
    dsimp only [p,q]
    calc
      _ = r*(star r*s)*star s := by noncomm_ring
      _ = _ := by rw [hrs,mul_zero,zero_mul]
  have hqp : q*p=0 := by
    simpa only [star_mul,hp,hq,star_zero] using congrArg star hpq
  have h := star_mul_self_nonneg (1-p-q)
  have he : star (1-p-q)*(1-p-q)=1-(p+q) := by
    simp only [star_sub,star_one,hp,hq]
    calc
      _ = 1-p-p+p*p-q-q+p*q+q*p+q*q := by noncomm_ring
      _ = _ := by rw [hpp,hqq,hpq,hqp]; noncomm_ring
  rw [he] at h
  exact sub_nonneg.mp h

lemma rowContraction_cross_norm_sq_le (x y : A)
    (hrow : x*star x+y*star y≤1) (hy : ‖y‖≤1) :
    ‖star x*y‖^2≤‖1-star y*y‖ := by
  have hp := star_left_conjugate_nonneg (sub_nonneg.mpr hrow) y
  have hord : star (star x*y)*(star x*y)≤ star y*y*(1-star y*y) := by
    apply sub_nonneg.mp
    convert hp using 1
    simp only [star_mul,star_star]
    noncomm_ring
  have hn := CStarAlgebra.norm_le_norm_of_le_of_nonneg
    hord (star_mul_self_nonneg (star x*y))
  have hy' : ‖star y*y‖≤1 := by
    calc
      _ ≤ ‖star y‖*‖y‖ := norm_mul_le _ _
      _ ≤ 1*1 := by rw [norm_star]; gcongr
      _ = _ := by ring
  calc
    _ = ‖star (star x*y)*(star x*y)‖ := by rw [CStarRing.norm_star_mul_self]; ring
    _ ≤ ‖star y*y*(1-star y*y)‖ := hn
    _ ≤ ‖star y*y‖*‖1-star y*y‖ := norm_mul_le _ _
    _ ≤ 1*‖1-star y*y‖ := mul_le_mul_of_nonneg_right hy' (norm_nonneg _)
    _ = _ := one_mul _

end Range

section CP

variable {A : Type u} {B : Type v} [CStarAlgebra A] [CStarAlgebra B]
  [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]

lemma cpc_cuntzPair_range_sum_le_one {φ : A →L[ℂ] B}
    (hφ : CompletelyPositive φ) (hφn : ‖φ‖≤1)
    (r s : A) (hr : star r*r=1) (hs : star s*s=1) (hrs : star r*s=0) :
    φ r*star (φ r)+φ s*star (φ s)≤1 := by
  have hr' : φ r*star (φ r)≤φ (r*star r) := by
    simpa only [star_star,completelyPositive_map_star hφ] using
      completelyPositive_schwarz hφ hφn (star r)
  have hs' : φ s*star (φ s)≤φ (s*star s) := by
    simpa only [star_star,completelyPositive_map_star hφ] using
      completelyPositive_schwarz hφ hφn (star s)
  have hrow := completelyPositive_map_nonneg hφ
    (sub_nonneg.mpr (cuntzPair_range_sum_le_one r s hr hs hrs))
  rw [map_sub,map_add,sub_nonneg] at hrow
  exact (add_le_add hr' hs').trans (hrow.trans (completelyPositive_one_le_one hφ hφn))

lemma cpc_cuntzPair_errors {φ : A →L[ℂ] B}
    (hφ : CompletelyPositive φ) (hφn : ‖φ‖≤1)
    (r s : A) (hr : star r*r=1) (hs : star s*s=1) (hrs : star r*s=0) :
    ‖star (φ r)*φ r-1‖≤‖φ 1-1‖+‖φ 1-star (φ r)*φ r‖ ∧
    ‖star (φ s)*φ s-1‖≤‖φ 1-1‖+‖φ 1-star (φ s)*φ s‖ ∧
    ‖star (φ r)*φ s‖^2≤‖φ 1-1‖+‖φ 1-star (φ s)*φ s‖ := by
  have herr (z : B) : ‖z-1‖≤‖φ 1-1‖+‖φ 1-z‖ := by
    calc
      _ ≤ ‖z-φ 1‖+‖φ 1-1‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ = _ := by rw [norm_sub_rev z]; ring
  have hsn : ‖s‖≤1 := by
    have hn := congrArg norm hs
    rw [CStarRing.norm_star_mul_self] at hn
    have h1 : ‖(1:A)‖≤1 := cstar_norm_one_le_one
    nlinarith [norm_nonneg s]
  have hφs : ‖φ s‖≤1 := (φ.le_opNorm s).trans ((mul_le_mul hφn hsn
    (norm_nonneg _) zero_le_one).trans (by norm_num))
  refine ⟨herr _,herr _,?_⟩
  have hc := rowContraction_cross_norm_sq_le (φ r) (φ s)
    (cpc_cuntzPair_range_sum_le_one hφ hφn r s hr hs hrs) hφs
  rw [norm_sub_rev 1] at hc
  exact hc.trans (herr _)

end CP

end

end WeakPureInfiniteness
end

end OAI
