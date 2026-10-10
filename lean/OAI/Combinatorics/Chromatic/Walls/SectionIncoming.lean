import Mathlib
import OAI.Combinatorics.Chromatic.Walls.TranslatedCompletion

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesAdjoint
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I]
variable (v : (LaurentSeries ℚ)ˣ) (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
local instance sectionIncomingAddCommGroup : AddCommGroup (Torus v Ω) := (Torus.instRing v Ω).toAddCommGroup
local instance sectionIncomingAddGroup : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
local instance sectionIncomingSub : Sub (Torus v Ω) := (Torus.instRing v Ω).toSub
attribute [local instance] Classical.propDecidable
variable (F : CompletedPositive v Ω C) (b : M)

def sectionIncoming (n : ℕ) (X : PowerSeries (Torus v Ω)) : Torus v Ω :=
  Finsupp.onFinset (shiftRootGrade_finite C b n).toFinset
    (fun m => if HasRootDegree C n (m-b) then
      (coeff n (sectionValue v Ω C F (incomingCovector Ω m) X)) m else 0)
    (by intro m hm; rw [Set.Finite.mem_toFinset]; by_contra hn; exact hm (ite_eq_right hn))
lemma sectionIncoming_apply (n : ℕ) (X : PowerSeries (Torus v Ω)) (m : M) :
    sectionIncoming v Ω C F b n X m=if HasRootDegree C n (m-b) then
      (coeff n (sectionValue v Ω C F (incomingCovector Ω m) X)) m else 0 := rfl
lemma sectionIncoming_graded (n : ℕ) (X : PowerSeries (Torus v Ω)) :
    sectionIncoming v Ω C F b n X∈shiftRootGrade v Ω C b n := by
  intro m hm
  rw [sectionIncoming_apply,ite_eq_right hm]
lemma sectionIncoming_congr (n : ℕ) (X Y : PowerSeries (Torus v Ω))
    (h : ∀k≤n,coeff k X=coeff k Y) :
    sectionIncoming v Ω C F b n X=sectionIncoming v Ω C F b n Y := by
  apply Finsupp.ext
  intro m
  rw [sectionIncoming_apply,sectionIncoming_apply]
  split_ifs
  · exact congrArg (fun t : Torus v Ω=>t m)
      (adjoint_coeff_congr (chartNegative v Ω C (incomingCovector Ω m) F).val _ X Y n (fun _ _=>rfl) h)
  · rfl
lemma sectionIncoming_leading (n : ℕ) (X Y : PowerSeries (Torus v Ω))
    (h : ∀k<n,coeff k X=coeff k Y)
    (hX : coeff n X∈shiftRootGrade v Ω C b n)
    (hY : coeff n Y∈shiftRootGrade v Ω C b n) :
    sectionIncoming v Ω C F b n X-sectionIncoming v Ω C F b n Y=coeff n X-coeff n Y := by
  apply Finsupp.ext
  intro m
  rw [torus_sub_apply,torus_sub_apply,sectionIncoming_apply,sectionIncoming_apply]
  by_cases hm : HasRootDegree C n (m-b)
  · rw [ite_eq_left hm,ite_eq_left hm]
    have H:=adjoint_leading (chartNegative v Ω C (incomingCovector Ω m) F).val X Y
      (chartNegative v Ω C (incomingCovector Ω m) F).property.1 n h
    simpa only [torus_sub_apply,sectionValue] using congrArg (fun t : Torus v Ω=>t m) H
  · rw [ite_eq_right hm,ite_eq_right hm,hX m hm,hY m hm]
lemma sectionIncoming_zero (X : PowerSeries (Torus v Ω))
    (hX : coeff 0 X∈shiftRootGrade v Ω C b 0) :
    sectionIncoming v Ω C F b 0 X=coeff 0 X := by
  apply Finsupp.ext
  intro m
  rw [sectionIncoming_apply]
  by_cases hm : HasRootDegree C 0 (m-b)
  · rw [ite_eq_left hm]
    unfold sectionValue
    rw [coeff_zero_eq_constantCoeff,constant_adjoint _ _ (chartNegative v Ω C _ F).property.1]
  · rw [ite_eq_right hm,hX m hm]

def sectionSolutionCoefficients (l : ℕ → Torus v Ω) : ℕ → Torus v Ω
  | 0 => l 0
  | n+1 => l (n+1)-sectionIncoming v Ω C F b (n+1)
    (PowerSeries.mk (fun k=>if _ : k≤n then sectionSolutionCoefficients l k else 0))
termination_by n=>n

def sectionSolution (l : ℕ → Torus v Ω) : PowerSeries (Torus v Ω) :=
  PowerSeries.mk (sectionSolutionCoefficients v Ω C F b l)
def sectionTruncation (l : ℕ → Torus v Ω) (n : ℕ) : PowerSeries (Torus v Ω) :=
  PowerSeries.mk (fun k=>if k≤n then sectionSolutionCoefficients v Ω C F b l k else 0)
lemma sectionSolution_graded (l : ℕ → Torus v Ω)
    (hl : ∀n,l n∈shiftRootGrade v Ω C b n) :
    ShiftGraded v Ω C b (sectionSolution v Ω C F b l) := by
  intro n
  cases n with
  | zero => simpa only [sectionSolution,coeff_mk,sectionSolutionCoefficients] using hl 0
  | succ n =>
    simp only [sectionSolution,coeff_mk,sectionSolutionCoefficients]
    exact (shiftRootGrade v Ω C b (n+1)).sub_mem (hl _) (sectionIncoming_graded v Ω C F b _ _)
lemma sectionTruncation_lower (l : ℕ → Torus v Ω) (n k : ℕ) (hk : k≤n) :
    coeff k (sectionSolution v Ω C F b l)=coeff k (sectionTruncation v Ω C F b l n) := by
  simp only [sectionSolution,sectionTruncation,coeff_mk,ite_eq_left hk]
lemma sectionTruncation_top (l : ℕ → Torus v Ω) (n : ℕ) :
    coeff (n+1) (sectionTruncation v Ω C F b l n)=0 := by
  simp only [sectionTruncation,coeff_mk,show ¬n+1≤n by omega,ite_false]
lemma sectionSolution_step (l : ℕ → Torus v Ω) (n : ℕ) :
    coeff (n+1) (sectionSolution v Ω C F b l)=l (n+1)-
      sectionIncoming v Ω C F b (n+1) (sectionTruncation v Ω C F b l n) := by
  simp only [sectionSolution,coeff_mk,sectionSolutionCoefficients,sectionTruncation,dite_eq_ite]
lemma sectionSolution_prescription (l : ℕ → Torus v Ω)
    (hl : ∀n,l n∈shiftRootGrade v Ω C b n) (n : ℕ) :
    sectionIncoming v Ω C F b n (sectionSolution v Ω C F b l)=l n := by
  cases n with
  | zero =>
    rw [sectionIncoming_zero v Ω C F b _ (sectionSolution_graded v Ω C F b l hl 0)]
    simp only [sectionSolution,coeff_mk,sectionSolutionCoefficients]
  | succ n =>
    have ht : coeff (n+1) (sectionTruncation v Ω C F b l n)∈shiftRootGrade v Ω C b (n+1):=by
      rw [sectionTruncation_top]; exact (shiftRootGrade v Ω C b (n+1)).zero_mem
    have H:=sectionIncoming_leading v Ω C F b (n+1)
      (sectionSolution v Ω C F b l) (sectionTruncation v Ω C F b l n)
      (fun k hk=>sectionTruncation_lower v Ω C F b l n k (by omega))
      (sectionSolution_graded v Ω C F b l hl _) ht
    rw [sectionTruncation_top,sub_zero,sectionSolution_step] at H
    exact sub_left_inj.mp H

theorem existsUnique_section (l : ℕ → Torus v Ω)
    (hl : ∀n,l n∈shiftRootGrade v Ω C b n) :
    ∃! X : {X : PowerSeries (Torus v Ω) // ShiftGraded v Ω C b X},
      ∀n,sectionIncoming v Ω C F b n X.val=l n := by
  refine ⟨⟨sectionSolution v Ω C F b l,sectionSolution_graded v Ω C F b l hl⟩,
    sectionSolution_prescription v Ω C F b l hl,?_⟩
  intro X hX
  apply Subtype.ext
  apply PowerSeries.ext
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have H:=sectionIncoming_leading v Ω C F b n X.val (sectionSolution v Ω C F b l)
      ih (X.property n) (sectionSolution_graded v Ω C F b l hl n)
    rw [hX n,sectionSolution_prescription v Ω C F b l hl n,sub_self] at H
    exact sub_eq_zero.mp H.symm

def thetaInitial : PowerSeries (Torus v Ω) :=
  sectionSolution v Ω C F b (fun n=>coeff n (PowerSeries.C (Torus.X v Ω b)))
def thetaValue (h : M →+ ℝ) : PowerSeries (Torus v Ω) :=
  sectionValue v Ω C F h (thetaInitial v Ω C F b)
lemma thetaInitial_graded : ShiftGraded v Ω C b (thetaInitial v Ω C F b) :=
  sectionSolution_graded v Ω C F b _ (ShiftGraded.monomial v Ω C b)
lemma thetaValue_graded (h : M →+ ℝ) : ShiftGraded v Ω C b (thetaValue v Ω C F b h) :=
  (thetaInitial_graded v Ω C F b).sectionValue v Ω C F h
lemma thetaInitial_prescription (n : ℕ) :
    sectionIncoming v Ω C F b n (thetaInitial v Ω C F b)=
      coeff n (PowerSeries.C (Torus.X v Ω b)) :=
  sectionSolution_prescription v Ω C F b _ (ShiftGraded.monomial v Ω C b) n
lemma thetaValue_leading (h : M →+ ℝ) :
    constantCoeff (thetaValue v Ω C F b h)=Torus.X v Ω b := by
  rw [thetaValue,sectionValue,constant_adjoint _ _ (chartNegative v Ω C h F).property.1]
  simp only [thetaInitial,sectionSolution,←coeff_zero_eq_constantCoeff_apply,coeff_mk,sectionSolutionCoefficients,coeff_C,ite_true]
end
end ElementaryPositivity.QuantumTorus

end

end OAI
