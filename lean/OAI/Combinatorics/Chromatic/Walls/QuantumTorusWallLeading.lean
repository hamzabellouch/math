import Mathlib
import OAI.Combinatorics.Chromatic.Walls.QuantumTorusChartCompletion
import OAI.Combinatorics.Chromatic.GradedAlgebra.PowerSeriesProductLeading

namespace OAI

section
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries ElementaryPositivity.PowerSeriesSplit
noncomputable section
variable {R M I A : Type*} [CommRing R] [AddCommGroup M] [Fintype I]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M) (h : M →+ ℝ)
local instance : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
local instance : Sub (Torus v Ω) := (Torus.instRing v Ω).toSub

omit [Fintype I] in
lemma zero_positive_project (x : Torus v Ω) :
    zeroProject v Ω h (positiveProject v Ω h x)=0 := by
  classical
  ext m
  change (x.filter (fun m=>0<h m) |>.filter (fun m=>h m=0)) m=0
  simp only [Finsupp.filter_apply]
  split_ifs <;> first | rfl | linarith

lemma chartZero_leading_difference (f g : CompletedPositive v Ω C) (n : ℕ)
    (hlow : ∀k≤n,coeff k f.val=coeff k g.val) :
    coeff (n+1) (chartZero v Ω C h f).val-
      coeff (n+1) (chartZero v Ω C h g).val=
      zeroProject v Ω h (coeff (n+1) f.val-coeff (n+1) g.val) :=
  zero_leading_difference (positiveProject v Ω h) (zeroProject v Ω h)
    (zero_positive_project v Ω h) f.val g.val n hlow

omit [Fintype I] in
lemma joint_middle_leading_difference (f g : A → PowerSeries (Torus v Ω))
    (l : List A) (n : ℕ)
    (hf : ∀a∈l,constantCoeff (f a)=1) (hg : ∀a∈l,constantCoeff (g a)=1)
    (hlow : ∀a∈l,∀k≤n,coeff k (f a)=coeff k (g a)) :
    coeff (n+1) (zeroFactor (positiveProject v Ω h) (zeroProject v Ω h) (l.map f).prod)-
      coeff (n+1) (zeroFactor (positiveProject v Ω h) (zeroProject v Ω h) (l.map g).prod)=
      zeroProject v Ω h
        (l.map (fun a=>coeff (n+1) (f a)-coeff (n+1) (g a))).sum := by
  rw [zero_leading_difference (positiveProject v Ω h) (zeroProject v Ω h)
    (zero_positive_project v Ω h) _ _ n
    (fun k hk=>product_coeff_congr f g l k (fun a ha j hj=>hlow a ha j (hj.trans hk)))]
  rw [product_leading_difference f g l n hf hg hlow]

omit [Fintype I] in
lemma joint_middle_monomial_unaffected (f g : A → PowerSeries (Torus v Ω))
    (l : List A) (n : ℕ) (m : M)
    (hf : ∀a∈l,constantCoeff (f a)=1) (hg : ∀a∈l,constantCoeff (g a)=1)
    (hlow : ∀a∈l,∀k≤n,coeff k (f a)=coeff k (g a))
    (hlast : ∀a∈l,coeff (n+1) (f a) m=coeff (n+1) (g a) m) :
    coeff (n+1) (zeroFactor (positiveProject v Ω h) (zeroProject v Ω h) (l.map f).prod) m=
      coeff (n+1) (zeroFactor (positiveProject v Ω h) (zeroProject v Ω h) (l.map g).prod) m := by
  classical
  have eval_sub (x y : Torus v Ω) : (x-y) m=x m-y m := by
    change x m + -y m=x m-y m
    exact (sub_eq_add_neg _ _).symm
  have he:=congrArg (fun x : Torus v Ω=>x m)
    (joint_middle_leading_difference v Ω h f g l n hf hg hlow)
  rw [eval_sub] at he
  change _-_=((l.map (fun a=>coeff (n+1) (f a)-coeff (n+1) (g a))).sum.filter
    (fun x=>h x=0)) m at he
  rw [Finsupp.filter_apply] at he
  have hz : (l.map (fun a=>coeff (n+1) (f a)-coeff (n+1) (g a))).sum m=0 := by
    clear he hf hg hlow
    induction l with
    | nil => rfl
    | cons a l ih =>
      simp only [List.map_cons,List.sum_cons,Finsupp.add_apply]
      rw [eval_sub,hlast a List.mem_cons_self,sub_self,zero_add]
      exact ih (fun b hb=>hlast b (List.mem_cons_of_mem a hb))
  rw [hz,ite_self] at he
  exact sub_eq_zero.mp he
end
end ElementaryPositivity.QuantumTorus
end
end

end OAI
