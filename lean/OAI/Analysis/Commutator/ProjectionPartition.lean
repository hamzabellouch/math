import Mathlib

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators

namespace Kadison.SpectralPartition

variable {R : Type*} [Ring R] [StarRing R]

omit [StarRing R] in
lemma swap_middle (a b c d : R) (hc : Commute b c) :
    (a*b)*(c*d)=(a*c)*(b*d) := by
  calc
    (a*b)*(c*d)=a*((b*c)*d) := by simp only [mul_assoc]
    _=a*((c*b)*d) := by rw [hc.eq]
    _=(a*c)*(b*d) := by simp only [mul_assoc]

def splitPiece (p : R) (b : Bool) : R := if b then p else 1-p

lemma splitPiece_projection {p : R} (hp : IsStarProjection p) (b : Bool) :
    IsStarProjection (splitPiece p b) := by
  cases b
  · exact hp.one_sub
  · exact hp

omit [StarRing R] in
lemma splitPiece_commute {p a : R} (h : Commute a p) (b : Bool) :
    Commute a (splitPiece p b) := by
  cases b
  · exact (Commute.one_right a).sub_right h
  · exact h

lemma splitPiece_orthogonal {p : R} (hp : IsStarProjection p) {b c : Bool} (h : b≠c) :
    splitPiece p b*splitPiece p c=0 := by
  cases b <;> cases c <;> simp_all [splitPiece,mul_sub,sub_mul,hp.isIdempotentElem.eq]

omit [StarRing R] in
lemma splitPiece_sum (p : R) : (∑ b : Bool,splitPiece p b)=1 := by
  simp [splitPiece]

theorem exists_partition (n : ℕ) (p : Fin n → R)
    (hp : ∀ i,IsStarProjection (p i)) (hc : ∀ i j,Commute (p i) (p j)) :
    ∃ (J : Type) (_ : Fintype J) (e : J → R),
      (∀ j,IsStarProjection (e j)) ∧
      (∀ j k,j≠k → e j*e k=0) ∧
      (∑ j,e j)=1 ∧
      (∀ i,∃ χ : J → Bool,p i=∑ j,if χ j then e j else 0) ∧
      (∀ a : R,(∀ i,Commute a (p i)) → ∀ j,Commute a (e j)) := by
  classical
  induction n with
  | zero =>
    refine ⟨Unit,inferInstance,fun _ => 1,fun _ => IsStarProjection.one R,?_,?_,?_,?_⟩
    · intro j k h; exact (h (Subsingleton.elim _ _)).elim
    · simp
    · intro i; exact Fin.elim0 i
    · intro a h j; exact Commute.one_right a
  | succ n ih =>
    obtain ⟨J,hJ,e,he,ho,hs,hr,ha⟩ := ih (fun i => p i.succ)
      (fun i => hp i.succ) (fun i j => hc i.succ j.succ)
    let : Fintype J := hJ
    have hpe (j : J) : Commute (p 0) (e j) := ha (p 0) (fun i => hc 0 i.succ) j
    let f : Bool × J → R := fun j => splitPiece (p 0) j.1*e j.2
    refine ⟨Bool×J,inferInstance,f,?_,?_,?_,?_,?_⟩
    · intro j
      exact (splitPiece_projection (hp 0) j.1).mul (he j.2)
        (splitPiece_commute (hpe j.2).symm j.1).symm
    · rintro ⟨b,j⟩ ⟨c,k⟩ h
      change (splitPiece (p 0) b*e j)*(splitPiece (p 0) c*e k)=0
      rw [swap_middle _ _ _ _ (splitPiece_commute (hpe j).symm c)]
      by_cases hj : j=k
      · have hbc : b≠c := fun hb => h (Prod.ext hb hj)
        rw [splitPiece_orthogonal (hp 0) hbc,zero_mul]
      · rw [ho j k hj,mul_zero]
    · change (∑ j : Bool×J,splitPiece (p 0) j.1*e j.2)=1
      rw [Fintype.sum_prod_type]
      simp only [←Finset.mul_sum,hs,mul_one]
      exact splitPiece_sum _
    · intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · refine ⟨fun j => j.1,?_⟩
        change p 0=∑ j : Bool×J,if j.1 then splitPiece (p 0) j.1*e j.2 else 0
        rw [Fintype.sum_prod_type,Fintype.sum_bool]
        simp only [Bool.false_eq_true,↓reduceIte,Finset.sum_const_zero,add_zero,splitPiece]
        rw [←Finset.mul_sum,hs,mul_one]
      · obtain ⟨χ,hχ⟩ := hr i
        refine ⟨fun j => χ j.2,?_⟩
        change p i.succ=∑ j : Bool×J,if χ j.2 then splitPiece (p 0) j.1*e j.2 else 0
        rw [Fintype.sum_prod_type,Fintype.sum_bool]
        simp only [splitPiece,↓reduceIte]
        rw [←Finset.sum_add_distrib,hχ]
        apply Finset.sum_congr rfl
        intro j hj
        by_cases hh : χ j=true
        · simp only [hh,Bool.false_eq_true,↓reduceIte,←add_mul]
          have hz : p 0+(1-p 0)=1 := by abel
          rw [hz,one_mul]
        · simp [hh]
    · intro a h j
      exact (splitPiece_commute (h 0) j.1).mul_right
        (ha a (fun i => h i.succ) j.2)

end Kadison.SpectralPartition

end

end
end

end OAI
