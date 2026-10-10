import OAI.Analysis.Laughlin.FourBody.HighestFock
import OAI.Analysis.Laughlin.FourBody.PhysicalTrace

namespace OAI

namespace Laughlin.Fock
open Rotation Spin
open scoped BigOperators Matrix

theorem fourWedgeUnit_family_sum (Q p j k : ℕ) (hp : p < 2*Q-2+1) (hj : j ≤ Q) (hk : k ≤ Q)
    (hjk : j < k) (v : FourWedgeIndex Q → Space Q) :
    (∑ i, (fourWedgeUnit Q p j k i : ℂ) • v i) =
      v (⟨p,hp⟩,⟨(⟨j,by omega⟩,⟨k,by omega⟩),hjk⟩) := by
  have he (i : FourWedgeIndex Q) :
      (i.1.val=p ∧ i.2.val.1.val=j ∧ i.2.val.2.val=k) ↔
        i=(⟨p,hp⟩,⟨(⟨j,by omega⟩,⟨k,by omega⟩),hjk⟩) := by
    constructor
    · rintro ⟨h1,h2,h3⟩
      exact Prod.ext (Fin.ext h1) (Subtype.ext (Prod.ext (Fin.ext h2) (Fin.ext h3)))
    · intro h; subst i; exact ⟨rfl,rfl,rfl⟩
  simp only [fourWedgeUnit,apply_ite,Complex.ofReal_one,Complex.ofReal_zero,ite_smul,one_smul,zero_smul]
  simp_rw [he]
  simp

theorem sourceFourEnd_swap (Q p : ℕ) (j k : Fin (Q+1)) :
    sourceFourEnd Q p k j = -sourceFourEnd Q p j k := by
  have h : annihilate j*annihilate k = -(annihilate k*annihilate j) :=
    eq_neg_of_add_eq_zero_left (annihilate_anticommute j k)
  rw [sourceFourEnd,sourceFourEnd,h]
  ext x
  rfl

theorem fourSignedUnit_family_sum (Q p j k : ℕ) (hp : p < 2*Q-2+1) (hj : j ≤ Q) (hk : k ≤ Q)
    (x : Space Q) :
    (∑ i, (fourSignedUnit Q p j k i : ℂ) • sourceFourFamilyEnd Q i x) =
      sourceFourEnd Q p ⟨j,by omega⟩ ⟨k,by omega⟩ x := by
  simp only [fourSignedUnit,Pi.sub_apply,Complex.ofReal_sub,sub_smul,Finset.sum_sub_distrib]
  rcases lt_trichotomy j k with h | h | h
  · rw [fourWedgeUnit_family_sum Q p j k hp hj hk h,fourWedgeUnit_zero Q p k j (by omega)]
    simp only [Pi.zero_apply,Complex.ofReal_zero,zero_smul,Finset.sum_const_zero,sub_zero]
    rfl
  · subst k
    rw [sub_self]
    simp only [sourceFourEnd,annihilate_sq,zero_mul,LinearMap.zero_apply]
  · rw [fourWedgeUnit_zero Q p j k (by omega),fourWedgeUnit_family_sum Q p k j hp hk hj h]
    simp only [Pi.zero_apply,Complex.ofReal_zero,zero_smul,Finset.sum_const_zero,zero_sub,
      sourceFourFamilyEnd,sourceFourEnd_swap Q p ⟨j,by omega⟩ ⟨k,by omega⟩,
      LinearMap.neg_apply,neg_neg]

theorem fourBodyTermMatrix_Fock (Q t : ℕ) (e f : ℕ × ℕ × ℤ)
    (he : t ≤ e.1+e.2.1) (hf : t ≤ f.1+f.2.1)
    (hQ : e.1+e.2.1+(f.1+f.2.1-t)+2 ≤ Q) (x : Space Q) :
    contractionForm Q (sourceFourFamilyEnd Q) ((fourBodyTermMatrix Q t e f).map Complex.ofReal) x =
      -(sourceAlpha t e * sourceAlpha t f : ℝ) * occupationInner Q
        (sourceFourEnd Q e.1 ⟨e.2.1,by omega⟩ ⟨f.1+f.2.1-t,by omega⟩ x)
        (sourceFourEnd Q f.1 ⟨f.2.1,by omega⟩ ⟨e.1+e.2.1-t,by omega⟩ x) := by
  have hm : (fourBodyTermMatrix Q t e f).map Complex.ofReal =
      (-(sourceAlpha t e * sourceAlpha t f : ℝ) : ℂ) •
        complexOuter (fun i => (fourSignedUnit Q e.1 e.2.1 (f.1+f.2.1-t) i : ℂ))
          (fun i => (fourSignedUnit Q f.1 f.2.1 (e.1+e.2.1-t) i : ℂ)) := by
    ext i j
    simp [fourBodyTermMatrix,realOuter,complexOuter]
  rw [hm,contractionForm_smul,contractionForm_outer_cross]
  simp only [Complex.star_def,Complex.conj_ofReal]
  rw [fourSignedUnit_family_sum Q e.1 e.2.1 (f.1+f.2.1-t) (by omega) (by omega) (by omega),
    fourSignedUnit_family_sum Q f.1 f.2.1 (e.1+e.2.1-t) (by omega) (by omega) (by omega)]

end Laughlin.Fock

end OAI
