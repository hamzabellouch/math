import Mathlib
import OAI.Combinatorics.Chromatic.Walls.CompletedInverse

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesAdjoint
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I]
variable (v : (LaurentSeries ℚ)ˣ) (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
local instance shiftRootGradeAddCommGroup : AddCommGroup (Torus v Ω) := (Torus.instRing v Ω).toAddCommGroup
local instance shiftRootGradeSub : Sub (Torus v Ω) := (Torus.instRing v Ω).toSub
local instance shiftRootGradeAddGroup : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup

def shiftRootGrade (b : M) (n : ℕ) : AddSubgroup (Torus v Ω) where
  carrier:={f | ∀m,¬HasRootDegree C n (m-b) → f m=0}
  zero_mem':=by intro m hm; rfl
  add_mem':=by intro f g hf hg m hm; change f m+g m=0; rw [hf m hm,hg m hm,add_zero]
  neg_mem':=by intro f hf m hm; change -f m=0; rw [hf m hm,neg_zero]
def ShiftGraded (b : M) (X : PowerSeries (Torus v Ω)) : Prop :=
  ∀n,coeff n X∈shiftRootGrade v Ω C b n
lemma shiftRootGrade_finite (b : M) (n : ℕ) : {m | HasRootDegree C n (m-b)}.Finite := by
  apply ((rootDegree_finite C n).image (fun r=>r+b)).subset
  intro m hm
  exact ⟨m-b,hm,sub_add_cancel m b⟩
lemma shiftRootGrade_mul (b c : M) (n k : ℕ) (f g : Torus v Ω)
    (hf : f∈shiftRootGrade v Ω C b n) (hg : g∈shiftRootGrade v Ω C c k) :
    f*g∈shiftRootGrade v Ω C (b+c) (n+k) := by
  classical
  intro m hm
  change (Torus.multiply v Ω f g) m=0
  simp only [Torus.multiply,Finsupp.sum,Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro x hx
  apply Finset.sum_eq_zero
  intro y hy
  have hxC : HasRootDegree C n (x-b):=by by_contra hn; exact (Finsupp.mem_support_iff.mp hx) (hf x hn)
  have hyC : HasRootDegree C k (y-c):=by by_contra hn; exact (Finsupp.mem_support_iff.mp hy) (hg y hn)
  apply Finsupp.single_eq_of_ne
  intro he
  apply hm
  rw [he]
  convert rootDegree_add C hxC hyC using 1; abel
lemma ShiftGraded.mul {b c : M} {X Y : PowerSeries (Torus v Ω)}
    (hX : ShiftGraded v Ω C b X) (hY : ShiftGraded v Ω C c Y) :
    ShiftGraded v Ω C (b+c) (X*Y) := by
  intro n
  rw [coeff_mul]
  apply (shiftRootGrade v Ω C (b+c) n).sum_mem
  intro p hp
  rw [←Finset.HasAntidiagonal.mem_antidiagonal.mp hp]
  exact shiftRootGrade_mul v Ω C b c p.1 p.2 _ _ (hX p.1) (hY p.2)
lemma shiftGraded_zero_iff (F : PowerSeries (Torus v Ω)) :
    ShiftGraded v Ω C 0 F↔SeriesGraded v Ω C F := by
  simp only [ShiftGraded,SeriesGraded,shiftRootGrade,rootGrade,AddSubgroup.mem_mk,sub_zero]
lemma ShiftGraded.adjoint {b : M} {X : PowerSeries (Torus v Ω)}
    (hX : ShiftGraded v Ω C b X) (F : CompletedPositive v Ω C) :
    ShiftGraded v Ω C b (adjoint F.val X) := by
  have hF:=(shiftGraded_zero_iff v Ω C F.val).mpr F.property.2
  have hI:=(shiftGraded_zero_iff v Ω C (completedInverse v Ω C F).val).mpr
    (completedInverse v Ω C F).property.2
  simpa only [zero_add,add_zero,PowerSeriesAdjoint.adjoint,completedInverse] using (hF.mul v Ω C hX).mul v Ω C hI
lemma ShiftGraded.sub {b : M} {X Y : PowerSeries (Torus v Ω)}
    (hX : ShiftGraded v Ω C b X) (hY : ShiftGraded v Ω C b Y) :
    ShiftGraded v Ω C b (X-Y) := by
  intro n
  exact (shiftRootGrade v Ω C b n).sub_mem (hX n) (hY n)
lemma ShiftGraded.monomial (b : M) :
    ShiftGraded v Ω C b (PowerSeries.C (Torus.X v Ω b)) := by
  intro n
  rw [coeff_C]
  split_ifs with hn
  · subst n
    intro m hm
    change (Finsupp.single b (1:LaurentSeries ℚ)) m=0
    apply Finsupp.single_eq_of_ne
    intro he
    apply hm
    rw [←he,sub_self]
    exact rootDegree_zero C
  · exact (shiftRootGrade v Ω C b n).zero_mem

def sectionValue (F : CompletedPositive v Ω C) (h : M →+ ℝ)
    (X : PowerSeries (Torus v Ω)) : PowerSeries (Torus v Ω) :=
  adjoint (chartNegative v Ω C h F).val X
lemma ShiftGraded.sectionValue {b : M} {X : PowerSeries (Torus v Ω)}
    (hX : ShiftGraded v Ω C b X) (F : CompletedPositive v Ω C) (h : M →+ ℝ) :
    ShiftGraded v Ω C b (sectionValue v Ω C F h X) :=
  hX.adjoint v Ω C (chartNegative v Ω C h F)
end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesAdjoint
noncomputable section
variable {M : Type*} [AddCommGroup M]
variable (v : (LaurentSeries ℚ)ˣ) (Ω : M →+ M →+ ℤ) (q : M →+ ℤ)
local instance chargeGradeAddCommGroup : AddCommGroup (Torus v Ω) := (Torus.instRing v Ω).toAddCommGroup
local instance chargeGradeAddGroup : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
local instance chargeGradeSub : Sub (Torus v Ω) := (Torus.instRing v Ω).toSub

def chargeGrade (z : ℤ) : AddSubgroup (Torus v Ω) where
  carrier:={f | ∀m,q m≠z → f m=0}
  zero_mem':=by intro m hm; rfl
  add_mem':=by intro f g hf hg m hm; change f m+g m=0; rw [hf m hm,hg m hm,add_zero]
  neg_mem':=by intro f hf m hm; change -f m=0; rw [hf m hm,neg_zero]
lemma chargeGrade_one : (1:Torus v Ω)∈chargeGrade v Ω q 0 := by
  intro m hm
  change (Finsupp.single 0 (1:LaurentSeries ℚ)) m=0
  apply Finsupp.single_eq_of_ne
  intro he
  exact hm (by rw [he,map_zero])
lemma chargeGrade_X (m : M) : Torus.X v Ω m∈chargeGrade v Ω q (q m) := by
  intro r hr
  change (Finsupp.single m (1:LaurentSeries ℚ)) r=0
  apply Finsupp.single_eq_of_ne
  exact fun he=>hr (congrArg q he)
lemma chargeGrade_mul (a b : ℤ) (f g : Torus v Ω)
    (hf : f∈chargeGrade v Ω q a) (hg : g∈chargeGrade v Ω q b) :
    f*g∈chargeGrade v Ω q (a+b) := by
  classical
  intro m hm
  change (Torus.multiply v Ω f g) m=0
  simp only [Torus.multiply,Finsupp.sum,Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro x hx
  apply Finset.sum_eq_zero
  intro y hy
  have hxq : q x=a:=by by_contra hn; exact (Finsupp.mem_support_iff.mp hx) (hf x hn)
  have hyq : q y=b:=by by_contra hn; exact (Finsupp.mem_support_iff.mp hy) (hg y hn)
  apply Finsupp.single_eq_of_ne
  intro he
  apply hm
  rw [he,map_add,hxq,hyq]
lemma chargeGrade_series_mul (a b : ℤ) (F G : PowerSeries (Torus v Ω)) (N : ℕ)
    (hF : ∀n≤N,coeff n F∈chargeGrade v Ω q a)
    (hG : ∀n≤N,coeff n G∈chargeGrade v Ω q b) :
    coeff N (F*G)∈chargeGrade v Ω q (a+b) := by
  rw [coeff_mul]
  apply (chargeGrade v Ω q (a+b)).sum_mem
  intro p hp
  have H:=Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  exact chargeGrade_mul v Ω q a b _ _ (hF p.1 (by omega)) (hG p.2 (by omega))
lemma chargeGrade_inverse (F : PowerSeries (Torus v Ω)) (N : ℕ)
    (hF : ∀n≤N,coeff n F∈chargeGrade v Ω q 0) :
    ∀n≤N,coeff n (invOfUnit F 1)∈chargeGrade v Ω q 0 := by
  intro n hn
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [coeff_inverse_one]
    split_ifs with h0
    · exact chargeGrade_one v Ω q
    · apply (chargeGrade v Ω q 0).neg_mem
      apply (chargeGrade v Ω q 0).sum_mem
      intro p hp
      split_ifs with hp2
      · have H:=Finset.HasAntidiagonal.mem_antidiagonal.mp hp
        simpa only [add_zero] using chargeGrade_mul v Ω q 0 0 _ _
          (hF p.1 (by omega)) (ih p.2 hp2 (by omega))
      · exact (chargeGrade v Ω q 0).zero_mem
lemma adjoint_charge (F : PowerSeries (Torus v Ω)) (N : ℕ)
    (hF : ∀n≤N,coeff n F∈chargeGrade v Ω q 0) (m : M) :
    coeff N (adjoint F (PowerSeries.C (Torus.X v Ω m)))∈chargeGrade v Ω q (q m) := by
  have hm : ∀n≤N,coeff n (PowerSeries.C (Torus.X v Ω m))∈chargeGrade v Ω q (q m):=by
    intro n hn
    rw [coeff_C]
    split_ifs
    · exact chargeGrade_X v Ω q m
    · exact (chargeGrade v Ω q (q m)).zero_mem
  have hFI : ∀n≤N,coeff n (F*PowerSeries.C (Torus.X v Ω m))∈chargeGrade v Ω q (q m):=by
    intro n hn
    simpa only [zero_add] using chargeGrade_series_mul v Ω q 0 (q m) _ _ n
      (fun j hj=>hF j (hj.trans hn)) (fun j hj=>hm j (hj.trans hn))
  simpa only [add_zero,adjoint] using chargeGrade_series_mul v Ω q (q m) 0 _ _ N hFI
    (chargeGrade_inverse v Ω q F N hF)
end
end ElementaryPositivity.QuantumTorus

end

end OAI
