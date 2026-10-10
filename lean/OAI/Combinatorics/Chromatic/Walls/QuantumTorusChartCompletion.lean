import Mathlib
import OAI.Combinatorics.Chromatic.Walls.PowerSeriesThreeFactors
import OAI.Combinatorics.Chromatic.GradedAlgebra.QuantumTorusSignFactors

namespace OAI

section
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries
noncomputable section
variable {R M I : Type*} [CommRing R] [AddCommGroup M] [Fintype I]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
local instance chartCompletionAddGroup : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup

def HasRootDegree (n : ℕ) (m : M) : Prop :=
  ∃d : I → ℕ,(∑i,d i)=n ∧ C (fun i=>(d i:ℤ))=m

lemma rootDegree_zero : HasRootDegree C 0 0 := by
  refine ⟨0,by simp,?_⟩
  change C (0 : I → ℤ)=0
  exact C.map_zero

lemma rootDegree_add {n k : ℕ} {m p : M}
    (hm : HasRootDegree C n m) (hp : HasRootDegree C k p) :
    HasRootDegree C (n+k) (m+p) := by
  obtain ⟨d,hd,hmd⟩:=hm
  obtain ⟨e,he,hpe⟩:=hp
  refine ⟨d+e,by simpa only [Pi.add_apply,Finset.sum_add_distrib] using congrArg₂ (·+·) hd he,?_⟩
  have hh : (fun i=>((d+e) i:ℤ))=(fun i=>(d i:ℤ))+(fun i=>(e i:ℤ)) := by
    ext i; simp
  rw [hh,map_add,hmd,hpe]

def rootGrade (n : ℕ) : AddSubgroup (Torus v Ω) where
  carrier := {f | ∀m,¬HasRootDegree C n m → f m=0}
  zero_mem' := by intro m hm; rfl
  add_mem' := by intro f g hf hg m hm; change f m+g m=0; rw [hf m hm,hg m hm,add_zero]
  neg_mem' := by intro f hf m hm; change -f m=0; rw [hf m hm,neg_zero]

lemma rootGrade_one : (1 : Torus v Ω)∈rootGrade v Ω C 0 := by
  intro m hm
  change Finsupp.single 0 (1:R) m=0
  apply Finsupp.single_eq_of_ne
  intro he
  exact hm (he ▸ rootDegree_zero C)

lemma rootGrade_mul (n k : ℕ) (f g : Torus v Ω)
    (hf : f∈rootGrade v Ω C n) (hg : g∈rootGrade v Ω C k) :
    f*g∈rootGrade v Ω C (n+k) := by
  classical
  intro m hm
  change (Torus.multiply v Ω f g) m=0
  simp only [Torus.multiply,Finsupp.sum,Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro x hx
  apply Finset.sum_eq_zero
  intro y hy
  have hxC : HasRootDegree C n x := by
    by_contra hn
    exact (Finsupp.mem_support_iff.mp hx) (hf x hn)
  have hyC : HasRootDegree C k y := by
    by_contra hn
    exact (Finsupp.mem_support_iff.mp hy) (hg y hn)
  apply Finsupp.single_eq_of_ne
  intro he
  exact hm (he ▸ rootDegree_add C hxC hyC)

lemma rootGrade_filter (p : M → Prop) [DecidablePred p] (n : ℕ) (f : Torus v Ω)
    (hf : f∈rootGrade v Ω C n) : f.filter p∈rootGrade v Ω C n := by
  intro m hm
  simp only [Finsupp.filter_apply,hf m hm,ite_self]

def CompletedPositive := {f : PowerSeries (Torus v Ω) //
  constantCoeff f=1 ∧ ∀n,coeff n f∈rootGrade v Ω C n}

variable (h : M →+ ℝ)
open ElementaryPositivity.PowerSeriesSplit

def chartPositive (f : CompletedPositive v Ω C) : CompletedPositive v Ω C :=
  ⟨positiveFactor (positiveProject v Ω h) f.val,left_constant _ _,
    (factors_graded (positiveProject v Ω h) (rootGrade v Ω C) (rootGrade_one v Ω C)
      (rootGrade_mul v Ω C) (fun n x hx=>rootGrade_filter v Ω C _ n x hx) f.val f.property.2).1⟩
def chartRemainder (f : CompletedPositive v Ω C) : CompletedPositive v Ω C :=
  ⟨rightFactor (positiveProject v Ω h) f.val,right_constant _ _,
    (factors_graded (positiveProject v Ω h) (rootGrade v Ω C) (rootGrade_one v Ω C)
      (rootGrade_mul v Ω C) (fun n x hx=>rootGrade_filter v Ω C _ n x hx) f.val f.property.2).2⟩
def chartZero (f : CompletedPositive v Ω C) : CompletedPositive v Ω C :=
  ⟨leftFactor (zeroProject v Ω h) (chartRemainder v Ω C h f).val,left_constant _ _,
    (factors_graded (zeroProject v Ω h) (rootGrade v Ω C) (rootGrade_one v Ω C)
      (rootGrade_mul v Ω C) (fun n x hx=>rootGrade_filter v Ω C _ n x hx)
      _ (chartRemainder v Ω C h f).property.2).1⟩
def chartNegative (f : CompletedPositive v Ω C) : CompletedPositive v Ω C :=
  ⟨rightFactor (zeroProject v Ω h) (chartRemainder v Ω C h f).val,right_constant _ _,
    (factors_graded (zeroProject v Ω h) (rootGrade v Ω C) (rootGrade_one v Ω C)
      (rootGrade_mul v Ω C) (fun n x hx=>rootGrade_filter v Ω C _ n x hx)
      _ (chartRemainder v Ω C h f).property.2).2⟩

lemma chart_three_factorization (f : CompletedPositive v Ω C) :
    (chartPositive v Ω C h f).val * (chartZero v Ω C h f).val *
      (chartNegative v Ω C h f).val = f.val :=
  factor_three (positiveProject v Ω h) (zeroProject v Ω h) f.val f.property.1

lemma chart_three_support (f : CompletedPositive v Ω C) :
    (∀n m,coeff (n+1) (chartPositive v Ω C h f).val m≠0 → 0<h m) ∧
    (∀n m,coeff (n+1) (chartZero v Ω C h f).val m≠0 → h m=0) ∧
    (∀n m,coeff (n+1) (chartNegative v Ω C h f).val m≠0 → h m<0) := by
  classical
  have ht:=three_support (positiveProject v Ω h) (zeroProject v Ω h)
    (supportedSubring v Ω (nonpositiveCone h)) (nonpositive_iff v Ω h)
    (positiveProject_idem v Ω h) (zeroProject_idem v Ω h) (positive_zero_project v Ω h) f.val
  constructor
  · intro n m hm
    exact (Finsupp.filter_eq_self_iff _ _).mp (ht.1 n) m hm
  constructor
  · intro n m hm
    exact (Finsupp.filter_eq_self_iff _ _).mp (ht.2.2.1 n) m hm
  · intro n m hm
    have hpos:= (Finsupp.filter_eq_zero_iff _ _).mp (ht.2.2.2.1 (n+1)) m
    have hzero:= (Finsupp.filter_eq_zero_iff _ _).mp (ht.2.2.2.2 n) m
    by_contra hn
    have hnm : 0≤h m := le_of_not_gt hn
    rcases lt_or_eq_of_le hnm with hh|hh
    · exact hm (hpos hh)
    · exact hm (hzero hh.symm)

lemma positiveProject_one : positiveProject v Ω h (1 : Torus v Ω)=0 := by
  classical
  change Finsupp.filter (fun m=>0<h m) (Finsupp.single 0 (1:R))=0
  apply (Finsupp.filter_eq_zero_iff _ _).mpr
  intro m hm
  apply Finsupp.single_eq_of_ne
  intro he
  subst m
  simp at hm

lemma chart_three_unique (f a b c : CompletedPositive v Ω C)
    (he : a.val*b.val*c.val=f.val)
    (ha : ∀n m,coeff (n+1) a.val m≠0 → 0<h m)
    (hb : ∀n m,coeff (n+1) b.val m≠0 → h m=0)
    (hc : ∀n m,coeff (n+1) c.val m≠0 → h m<0) :
    a=chartPositive v Ω C h f ∧ b=chartZero v Ω C h f ∧ c=chartNegative v Ω C h f := by
  classical
  have haP : ∀n,positiveProject v Ω h (coeff (n+1) a.val)=coeff (n+1) a.val := by
    intro n
    exact (Finsupp.filter_eq_self_iff _ _).mpr (ha n)
  have hbP : ∀n,positiveProject v Ω h (coeff n b.val)=0 := by
    intro n
    cases n with
    | zero => rw [coeff_zero_eq_constantCoeff_apply,b.property.1]; exact positiveProject_one v Ω h
    | succ n =>
      apply (Finsupp.filter_eq_zero_iff _ _).mpr
      intro m hm
      by_contra hn
      have hh:=hb n m hn
      linarith
  have hcP : ∀n,positiveProject v Ω h (coeff n c.val)=0 := by
    intro n
    cases n with
    | zero => rw [coeff_zero_eq_constantCoeff_apply,c.property.1]; exact positiveProject_one v Ω h
    | succ n =>
      apply (Finsupp.filter_eq_zero_iff _ _).mpr
      intro m hm
      by_contra hn
      have hh:=hc n m hn
      linarith
  have hbQ : ∀n,zeroProject v Ω h (coeff (n+1) b.val)=coeff (n+1) b.val := by
    intro n
    exact (Finsupp.filter_eq_self_iff _ _).mpr (hb n)
  have hcQ : ∀n,zeroProject v Ω h (coeff (n+1) c.val)=0 := by
    intro n
    apply (Finsupp.filter_eq_zero_iff _ _).mpr
    intro m hm
    by_contra hn
    have hh:=hc n m hn
    linarith
  have hu:=three_uniqueness (positiveProject v Ω h) (zeroProject v Ω h)
    (supportedSubring v Ω (nonpositiveCone h)) (nonpositive_iff v Ω h)
    f.val a.val b.val c.val a.property.1 b.property.1 c.property.1 he haP hbP hcP hbQ hcQ
  exact ⟨Subtype.ext hu.1,Subtype.ext hu.2.1,Subtype.ext hu.2.2⟩

end
end ElementaryPositivity.QuantumTorus
end
end

end OAI
