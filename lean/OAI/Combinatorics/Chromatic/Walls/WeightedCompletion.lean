import Mathlib
import OAI.Combinatorics.Chromatic.GradedAlgebra.SplitContinuity
import OAI.Combinatorics.Chromatic.GradedAlgebra.HNSeries

namespace OAI

section
namespace ElementaryPositivity.WeightedTorusSeries
open QuantumTorus PowerSeries LaurentPrecision
noncomputable section
variable {I J M ι : Type*} [Fintype I] [DecidableEq I] [Fintype J] [AddCommGroup M]
variable (w : I→ℕ) [Fact (∀i,0<w i)]
variable (v : (LaurentSeries ℚ)ˣ) (Ω : M→+M→+ℤ) (P : (I→ℕ)→+M)
variable (C : (J→ℤ)→+M) (hroot : ∀d,HasRootDegree C (weight w d) (P d))
local instance : Ring (Torus v Ω) := Torus.instRing v Ω
local instance : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid

local instance : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup

lemma torus_sum_apply {α : Type*} (s : Finset α) (f : α→Torus v Ω) (m : M) :
    (∑a∈s,f a) m=∑a∈s,f a m := by
  classical
  induction s using Finset.induction_on with
  | empty=>rfl
  | @insert a s ha ih=>
    rw [Finset.sum_insert ha,Finset.sum_insert ha]
    change (f a) m+(∑i∈s,f i) m=_
    rw [ih]

omit [DecidableEq I] in
include hroot in
lemma push_graded (f : (I→ℕ)→LaurentSeries ℚ) : SeriesGraded v Ω C (push w v Ω P f) := by
  classical
  intro n m hm
  simp only [push,coeff_mk,pushCoeff,torus_sum_apply]
  apply Finset.sum_eq_zero
  intro d hd
  change (Finsupp.single (P d.val) (f d.val)) m=0
  apply Finsupp.single_eq_of_ne
  intro H
  apply hm
  simpa only [d.property,H] using hroot d.val

def completedPush (f : (I→ℕ)→LaurentSeries ℚ) (hf : f 0=1) : CompletedPositive v Ω C :=
  ⟨push w v Ω P f,push_constant w v Ω P f hf,push_graded w v Ω P C hroot f⟩

variable (l : Filter ι)
omit [DecidableEq I] in
lemma push_converges {f : ι→(I→ℕ)→LaurentSeries ℚ} {F : (I→ℕ)→LaurentSeries ℚ}
    (hf : ∀d,Converges l (fun i=>f i d) (F d)) :
    SeriesConverges v Ω l (fun i=>push w v Ω P (f i)) (push w v Ω P F) := by
  classical
  intro n m
  simp only [push,coeff_mk,pushCoeff,torus_sum_apply]
  apply LaurentPrecision.Converges.sum
  intro d hd
  change Converges l (fun i=>(Finsupp.single (P d.val) (f i d.val)) m)
    ((Finsupp.single (P d.val) (F d.val)) m)
  by_cases H : m=P d.val
  · subst m
    simpa only [Finsupp.single_eq_same] using hf d.val
  · simp only [Finsupp.single_eq_of_ne H]
    exact converges_const l 0
end
end ElementaryPositivity.WeightedTorusSeries

end

end OAI
