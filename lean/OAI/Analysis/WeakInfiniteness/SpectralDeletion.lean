import Mathlib

namespace OAI

noncomputable section

namespace WeakPureInfiniteness

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



open scoped BigOperators CStarAlgebra

section PositiveDiagonal

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma sqrt_mul_eq_zero_of_sandwich_eq_zero {a e : A} (ha : 0 ≤ a)
    (he : IsSelfAdjoint e) (h : e*a*e=0) : CFC.sqrt a*e=0 := by
  apply (CStarRing.star_mul_self_eq_zero_iff _).mp
  rw [star_mul,he.star_eq,(CFC.sqrt_nonneg a).star_eq]
  calc
    (e*CFC.sqrt a)*(CFC.sqrt a*e)=e*(CFC.sqrt a*CFC.sqrt a)*e := by noncomm_ring
    _ = 0 := by rw [CFC.sqrt_mul_sqrt_self a ha,h]

end PositiveDiagonal

section UnitPartition

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {ι : Type*} [Fintype ι]

lemma eq_zero_of_nonneg_of_partition_diagonals {a : A} (ha : 0 ≤ a)
    (e : ι → A) (he : ∀ i, IsSelfAdjoint (e i)) (hs : ∑ i,e i=1)
    (hd : ∀ i,e i*a*e i=0) : a=0 := by
  have hz : CFC.sqrt a=0 := by
    calc
      CFC.sqrt a=CFC.sqrt a*(∑ i,e i) := by rw [hs,mul_one]
      _ = ∑ i,CFC.sqrt a*e i := Finset.mul_sum ..
      _ = 0 := by simp only [sqrt_mul_eq_zero_of_sandwich_eq_zero ha (he _) (hd _),
        Finset.sum_const_zero]
  exact (CFC.sqrt_eq_zero_iff a ha).mp hz

lemma both_signs_of_partition_diagonals {a : A} (ha : IsSelfAdjoint a) (hne : a ≠ 0)
    (e : ι → A) (he : ∀ i, IsSelfAdjoint (e i)) (hs : ∑ i,e i=1)
    (hd : ∀ i,e i*a*e i=0) : a⁺ ≠ 0 ∧ a⁻ ≠ 0 := by
  constructor
  · intro h
    have han : 0 ≤ -a := neg_nonneg.mpr ((CFC.posPart_eq_zero_iff a ha).mp h)
    have hz := eq_zero_of_nonneg_of_partition_diagonals han e he hs (by simpa using hd)
    exact hne (neg_eq_zero.mp hz)
  · intro h
    exact hne (eq_zero_of_nonneg_of_partition_diagonals
      ((CFC.negPart_eq_zero_iff a ha).mp h) e he hs hd)

end UnitPartition

section FiniteDeletion

variable {A : Type*} [NonUnitalCStarAlgebra A]

variable {ι κ : Type*} [Fintype ι]

def finiteDeletion (f : ι → A) (V : A) (R : ι → ι → Prop) [DecidableRel R] : A :=
  ∑ j, ∑ k, if R j k then f j*V*f k else 0

lemma finiteDeletion_selfAdjoint (f : ι → A) (V : A) (R : ι → ι → Prop)
    [DecidableRel R] (hf : ∀ j, IsSelfAdjoint (f j)) (hV : IsSelfAdjoint V)
    (hR : ∀ j k,R j k ↔ R k j) : IsSelfAdjoint (finiteDeletion f V R) := by
  show star (finiteDeletion f V R)=finiteDeletion f V R
  simp only [finiteDeletion, star_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  by_cases h : R j k
  · rw [ite_eq_left h,ite_eq_left ((hR j k).mp h),star_mul,star_mul,(hf j).star_eq,
      (hf k).star_eq,hV.star_eq]
    noncomm_ring
  · rw [ite_eq_right h,ite_eq_right (by simpa only [← hR j k] using h),star_zero]

lemma finiteDeletion_diagonals (f : ι → A) (V : A) (R : ι → ι → Prop)
    [DecidableRel R] (e : κ → A)
    (h : ∀ l j k,R j k → e l*f j=0 ∨ f k*e l=0) :
    ∀ l,e l*finiteDeletion f V R*e l=0 := by
  intro l
  simp only [finiteDeletion,Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_eq_zero
  intro j _
  apply Finset.sum_eq_zero
  intro k _
  by_cases hjk : R j k
  · rw [ite_eq_left hjk]
    rcases h l j k hjk with hleft | hright
    · rw [← mul_assoc,← mul_assoc,hleft,zero_mul,zero_mul,zero_mul]
    · calc
        e l*(f j*V*f k)*e l=e l*f j*V*(f k*e l) := by noncomm_ring
        _ = 0 := by rw [hright,mul_zero]
  · simp only [ite_eq_right hjk,mul_zero,zero_mul]

end FiniteDeletion


variable {A : Type*} [CStarAlgebra A]

variable {ι : Type*} [Fintype ι]

lemma finiteDeletion_preserves_corner (f : ι → A) (V p q : A)
    (R : ι → ι → Prop) [DecidableRel R] (hs : ∑ i,f i=1)
    (h : ∀ j k,¬R j k → p*f j=0 ∨ f k*q=0) :
    p*finiteDeletion f V R*q=p*V*q := by
  calc
    p*finiteDeletion f V R*q=∑ j,∑ k,p*(f j*V*f k)*q := by
      simp only [finiteDeletion,Finset.mul_sum,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      by_cases hjk : R j k
      · rw [ite_eq_left hjk]
      · rw [ite_eq_right hjk,mul_zero,zero_mul]
        rcases h j k hjk with hleft | hright
        · rw [← mul_assoc,← mul_assoc,hleft,zero_mul,zero_mul,zero_mul]
        · symm
          calc
            p*(f j*V*f k)*q=p*f j*V*(f k*q) := by noncomm_ring
            _ = 0 := by rw [hright,mul_zero]
    _ = p*((∑ j,f j)*V*(∑ k,f k))*q := by
      simp only [Finset.mul_sum,Finset.sum_mul]
      exact Finset.sum_comm
    _ = p*V*q := by rw [hs,one_mul,mul_one]




end WeakPureInfiniteness

end

end OAI
