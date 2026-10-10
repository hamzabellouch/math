import OAI.NumberTheory.DirichletL.Detector.HighEulerGeneral
import OAI.NumberTheory.DirichletL.Detector.HighDeletion

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic ProbeCompleted CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma outside_mul (S : Finset Id) (hS : ∀P∈S,Prime P) (A B : Id) :
    (∀P∈S,¬P∣A*B) ↔ (∀P∈S,¬P∣A) ∧ (∀P∈S,¬P∣B) := by
  constructor
  · intro h
    constructor
    · intro P hP hd
      exact h P hP ((hS P hP).dvd_mul.mpr (Or.inl hd))
    · intro P hP hd
      exact h P hP ((hS P hP).dvd_mul.mpr (Or.inr hd))
  · rintro ⟨hA,hB⟩ P hP hd
    exact ((hS P hP).dvd_mul.mp hd).elim (hA P hP) (hB P hP)

lemma outside_cube (S : Finset Id) (hS : ∀P∈S,Prime P) (A : Id) :
    (∀P∈S,¬P∣A^3) ↔ ∀P∈S,¬P∣A := by
  constructor
  · intro h P hP hd
    exact h P hP (dvd_trans hd (dvd_pow_self A (by decide : (3:ℕ)≠0)))
  · intro h P hP hd
    exact h P hP ((hS P hP).dvd_of_dvd_pow hd)

def highExclusion (S : Finset Id) (hS : ∀P∈S,Prime P) : Id→*ℂ where
  toFun A := if ∀P∈S,¬P∣A then 1 else 0
  map_one' := by
    rw [ite_eq_left]
    intro P hP hd
    exact (hS P hP).not_isUnit (isUnit_of_dvd_one hd)
  map_mul' A B := by
    simp only [outside_mul S hS A B]
    split_ifs <;> simp_all

lemma highExclusion_cube (S : Finset Id) (hS : ∀P∈S,Prime P) (A : Id) :
    highExclusion S hS (A^3)=highExclusion S hS A := by
  change (if ∀P∈S,¬P∣A^3 then (1:ℂ) else 0)=_
  simp only [outside_cube S hS]
  rfl

theorem highIdealMask_unmarked (S : Finset Id) (hS : ∀P∈S,Prime P) (I J K L : Id) :
    highIdealMask S 1 I J K L =
      highExclusion S hS I*highExclusion S hS J*highExclusion S hS K*highExclusion S hS L := by
  have he : completedMask S 1 I J=highExclusion S hS (I*J^3) := by
    simp only [completedMask,one_dvd,true_and]
    rfl
  unfold highIdealMask
  rw [he,map_mul,highExclusion_cube]
  rfl

lemma highIdealMask_unmarked_one (S : Finset Id) (hS : ∀P∈S,Prime P) :
    highIdealMask S 1 1 1 1 1=1 := by
  rw [highIdealMask_unmarked S hS]
  simp only [map_one,one_mul]

lemma highIdealMask_unmarked_mul (S : Finset Id) (hS : ∀P∈S,Prime P)
    (a b : HighIdeal) :
    highIdealMask S 1 (a.1.1*b.1.1) (a.1.2*b.1.2) (a.2.1*b.2.1) (a.2.2*b.2.2)=
      highIdealMask S 1 a.1.1 a.1.2 a.2.1 a.2.2 * highIdealMask S 1 b.1.1 b.1.2 b.2.1 b.2.2 := by
  simp only [highIdealMask_unmarked S hS,map_mul]
  ring

theorem excludedIdealHighSeries_hasProd (S : Finset Id) (hS : ∀P∈S,Prime P)
    (η : HeckeFamily.Character) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    HasProd (fun P : PrimeIdeal=>∑' b : HighValuation,
      markedIdealHighSummand S 1 η 1 x w z (P.val^b.1.1) (P.val^b.1.2) (P.val^b.2.1) (P.val^b.2.2))
      (markedIdealHighSeries S 1 η 1 x w z) := by
  apply highArray_hasProd (fun a : HighIdeal=>markedIdealHighSummand S 1 η 1 x w z a.1.1 a.1.2 a.2.1 a.2.2)
  · simp only [Prod.fst_one,Prod.snd_one,markedIdealHighSummand,
      highIdealMask_unmarked_one S hS,bareIdealHighSummand_one,one_mul]
  · intro a b hc
    simp only [Prod.fst_mul,Prod.snd_mul,markedIdealHighSummand,
      highIdealMask_unmarked_mul S hS a b,
      bareIdealHighSummand_mul η x w z _ _ _ _ _ _ _ _ hc]
    ring
  · intro a ha
    have hh : bareIdealHighSummand η 1 x w z a.1.1 a.1.2 a.2.1 a.2.2≠0 :=
      (mul_ne_zero_iff.mp ha).2
    have hs := bareIdealHighSummand_support η 1 x w z a.1.1 a.1.2 a.2.1 a.2.2 hh
    exact ⟨hs.2.1.1,hs.2.2.1.1,hs.2.2.2.1.1,hs.2.2.2.2.1⟩
  · exact (markedIdealHighSummand_summable S 1 η 1 x w z hx hw hz).norm

end SevenEighths.ProbePhysical
end

end OAI
