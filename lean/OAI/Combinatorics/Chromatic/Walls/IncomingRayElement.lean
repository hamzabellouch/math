import Mathlib
import OAI.Combinatorics.Chromatic.Walls.ChartRefinement
import OAI.Combinatorics.Chromatic.Walls.RayIncomingIdentification
import OAI.Combinatorics.Chromatic.GradedAlgebra.GradedFormalLog

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries
noncomputable section
variable {R M I : Type*} [CommRing R] [Algebra ℚ R] [AddCommGroup M] [Fintype I]
variable (v : Rˣ) (Ω : M→+M→+ℤ) (C : (I→ℤ)→+M)

lemma root_graded_log (F : CompletedPositive v Ω C) (n : ℕ) :
    coeff n (FormalLog.log F.val)∈rootGrade v Ω C n := by
  apply FormalLog.log_graded (rootGrade v Ω C) (rootGrade_one v Ω C)
    (rootGrade_mul v Ω C) _ F.val F.property.2 n
  intro j a x hx m hm
  change a • x m=0
  rw [hx m hm,smul_zero]

lemma OnPositiveRay.add {r a b : M} (ha : OnPositiveRay r a) (hb : OnPositiveRay r b) :
    OnPositiveRay r (a+b) := by
  obtain ⟨u,v,hu,hv,he⟩:=ha
  obtain ⟨s,t,hs,ht,hf⟩:=hb
  refine ⟨u*s,s*v+u*t,Nat.mul_pos hu hs,by positivity,?_⟩
  calc
    (u*s) • (a+b)=s • (u • a)+u • (s • b):=by
      rw [nsmul_add,mul_nsmul,mul_nsmul];
      congr 1; rw [←mul_nsmul,←mul_nsmul,Nat.mul_comm]
    _=s • (v • r)+u • (t • r):=by rw [he,hf]
    _=(s*v+u*t) • r:=by simp only [smul_smul,add_nsmul]

lemma incoming_ray_log_support (r : M) (k : M→+ℝ) (F : CompletedPositive v Ω C) (n : ℕ) :
    SupportedOn v Ω (fun m=>Ω m r=0 ∧ k m=0)
      (coeff n (FormalLog.log (chartZero v Ω C k
        (chartZero v Ω C (incomingCovector Ω r) F)).val)) := by
  let B:=chartZero v Ω C (incomingCovector Ω r) F
  let D:=chartZero v Ω C k B
  have hr:= (chartThree_supported v Ω C k (kernelSupport Ω r) B
    (incoming_chart_supported v Ω C r F)).2.1
  have hk:=chartZero_supported_kernel v Ω C k B
  apply strict_log_support v Ω
    (fun a b ha hb=>by
      constructor
      · simp only [map_add,AddMonoidHom.add_apply,ha.1,hb.1,add_zero]
      · simp only [map_add,ha.2,hb.2,add_zero])
    D.val D.property.1 _ n
  intro j m hm
  by_contra hx
  apply hm
  constructor
  · by_contra hn
    exact hx (hr (j+1) m hn)
  · by_contra hn
    exact hx (hk (j+1) m hn)

theorem incoming_ray_element_through (hΩ : ∀m,Ω m m=0) (r : M) (k : M→+ℝ)
    (hk : k r=0) (F D : CompletedPositive v Ω C) (N : ℕ)
    (hgeneric : ∀n,0<n→n≤N→∀m,HasRootDegree C n m→Ω m r=0→k m=0→OnPositiveRay r m)
    (hD : ∀n m,coeff (n+1) D.val m≠0→OnPositiveRay r m)
    (hprescribed : ∀n≤N,∀m,OnPositiveRay r m→
      coeff n (FormalLog.log (chartZero v Ω C (incomingCovector Ω m) F).val) m=
        coeff n (FormalLog.log D.val) m) :
    ∀n≤N,coeff n (chartZero v Ω C k
      (chartZero v Ω C (incomingCovector Ω r) F)).val=coeff n D.val := by
  let B:=chartZero v Ω C k (chartZero v Ω C (incomingCovector Ω r) F)
  apply FormalLog.log_injective_through B.val D.val N B.property.1 D.property.1
  intro n hn
  apply Finsupp.ext
  intro m
  by_cases hm : OnPositiveRay r m
  · exact (incoming_ray_log v Ω C hΩ r k hk F m hm n).trans (hprescribed n hn m hm)
  · have hD0:=strict_log_support v Ω (V:=OnPositiveRay r)
      (fun a b ha hb=>ha.add hb) D.val D.property.1
      (fun j m hm=>not_not.mp (fun hx=>hm (hD j m hx))) n m hm
    rw [hD0]
    by_cases hn0 : n=0
    · subst n
      simp only [coeff_zero_eq_constantCoeff,FormalLog.log_constant,Finsupp.zero_apply]
    · by_contra hx
      have hr : HasRootDegree C n m:=by
        by_contra hh; exact hx (root_graded_log v Ω C B n m hh)
      have hker : Ω m r=0 ∧ k m=0:=by
        by_contra hh; exact hx (incoming_ray_log_support v Ω C r k F n m hh)
      exact hm (hgeneric n (by omega) hn m hr hker.1 hker.2)
end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries
noncomputable section
variable {R M I : Type*} [CommRing R] [Algebra ℚ R] [AddCommGroup M] [Fintype I]
variable (v : Rˣ) (Ω : M→+M→+ℤ) (C : (I→ℤ)→+M)
local instance : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
local instance : Sub (Torus v Ω) := (Torus.instRing v Ω).toSub

lemma incoming_unique_through (hΩ : ∀m,Ω m m=0)
    (F G : CompletedPositive v Ω C) (N : ℕ)
    (H : ∀n≤N,incomingCoefficient v Ω C n F.val=incomingCoefficient v Ω C n G.val) :
    ∀n≤N,coeff n F.val=coeff n G.val := by
  intro n hn
  induction n using Nat.strong_induction_on with
  | h n ih=>
    cases n with
    | zero=>simp only [coeff_zero_eq_constantCoeff,F.property.1,G.property.1]
    | succ n=>
      have hEq:=incomingCoefficient_leading v Ω C hΩ F.val G.val n
        (fun j hj=>ih j (by omega) (by omega)) (F.property.2 _) (G.property.2 _)
      rw [H (n+1) hn,sub_self] at hEq
      exact sub_eq_zero.mp hEq.symm
end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries
noncomputable section
variable {R M I A : Type*} [CommRing R] [Algebra ℚ R] [AddCommGroup M] [Fintype I]
variable (v : Rˣ) (Ω : M→+M→+ℤ) (C : (I → ℤ)→+M)

omit [Algebra ℚ R] in
lemma completed_list_constant (l : List A) (F : A → CompletedPositive v Ω C) :
    constantCoeff (l.map (fun a=>(F a).val)).prod=1 := by
  induction l with
  | nil=>simp
  | cons a l ih=>simp only [List.map_cons,List.prod_cons,map_mul,(F a).property.1,ih,one_mul]
omit [Algebra ℚ R] in
lemma completed_list_graded (l : List A) (F : A → CompletedPositive v Ω C) :
    ∀n,coeff n (l.map (fun a=>(F a).val)).prod∈rootGrade v Ω C n := by
  induction l with
  | nil=>simpa using FormalLog.graded_one (rootGrade v Ω C) (rootGrade_one v Ω C)
  | cons a l ih=>
    simpa only [List.map_cons,List.prod_cons] using
      FormalLog.graded_multiply (rootGrade v Ω C) (rootGrade_mul v Ω C) _ _ (F a).property.2 ih

def completedListProduct (l : List A) (F : A → CompletedPositive v Ω C) : CompletedPositive v Ω C :=
  ⟨(l.map (fun a=>(F a).val)).prod,completed_list_constant v Ω C l F,completed_list_graded v Ω C l F⟩

omit [Algebra ℚ R] in
lemma completed_list_supported (l : List A) (F : A → CompletedPositive v Ω C)
    (V : AddSubmonoid M) (H : ∀a∈l,∀n,coeff n (F a).val∈supportedSubring v Ω V) :
    ∀n,coeff n (completedListProduct v Ω C l F).val∈supportedSubring v Ω V := by
  induction l with
  | nil=>
    intro n
    simp only [completedListProduct,List.map_nil,List.prod_nil,coeff_one]
    split_ifs
    · exact (supportedSubring v Ω V).one_mem
    · exact (supportedSubring v Ω V).zero_mem
  | cons a l ih=>
    exact PowerSeriesSplit.mul_mem (supportedSubring v Ω V) _ _ (H a (by simp))
      (ih (fun a ha=>H a (by simp [ha])))

lemma incoming_coefficient_supported (V : AddSubmonoid M) (F : CompletedPositive v Ω C)
    (H : ∀n,coeff n F.val∈supportedSubring v Ω V) (n : ℕ) :
    incomingCoefficient v Ω C n F.val∈supportedSubring v Ω V := by
  intro m hm
  rw [incomingCoefficient_apply]
  split_ifs with hr
  · exact strict_log_support v Ω (V:=fun x=>x∈V) (fun a b ha hb=>V.add_mem ha hb)
      (chartZero v Ω C (incomingCovector Ω m) F).val
      (chartZero v Ω C (incomingCovector Ω m) F).property.1
      (fun j=> (chartThree_supported v Ω C (incomingCovector Ω m) V F H).2.1 (j+1)) n m hm
  · rfl

omit [Algebra ℚ R] in
lemma strict_list_product_through (l : List A) (F : A → CompletedPositive v Ω C)
    (P : M → Prop) (hP : ∀a b,P a → P b → P (a+b)) (N : ℕ)
    (H : ∀a∈l,∀n,n+1≤N → SupportedOn v Ω P (coeff (n+1) (F a).val)) :
    ∀n,n+1≤N → SupportedOn v Ω P (coeff (n+1) (completedListProduct v Ω C l F).val) := by
  induction l with
  | nil=>intro n hn; simp only [completedListProduct,List.map_nil,List.prod_nil,coeff_one,show n+1≠0 by omega,ite_false]; exact SupportedOn.zero v Ω P
  | cons a l ih=>
    exact strict_mul_through v Ω P hP (F a).val (completedListProduct v Ω C l F).val N
      (F a).property.1 (completed_list_constant v Ω C l F) (H a (by simp))
      (ih (fun a ha=>H a (by simp [ha])))

omit [Algebra ℚ R] in
lemma ordered_ray_middle (hΩ : ∀m,Ω m m=0) (l : List M)
    (F : M → CompletedPositive v Ω C) (N : ℕ)
    (H : ∀p∈l,∀n,n+1≤N → ∀m,coeff (n+1) (F p).val m≠0 → OnPositiveRay p m)
    (hpair : l.Pairwise (fun a b=>0<Ω a b)) (p : M) (hp : p∈l) :
    ∀n≤N,coeff n (F p).val=
      coeff n (chartZero v Ω C (incomingCovector Ω p) (completedListProduct v Ω C l F)).val := by
  classical
  obtain ⟨a,b,he⟩:=List.mem_iff_append.mp hp
  subst l
  have hsplit:=List.pairwise_append.mp hpair
  have hbefore : ∀q∈a,0 < incomingCovector Ω p q:=by
    intro q hq
    change (0:ℝ)<(Ω q p:ℝ)
    exact_mod_cast hsplit.2.2 q hq p (by simp)
  have hafter : ∀q∈b,incomingCovector Ω p q<0:=by
    intro q hq
    have Hpq:=(List.pairwise_cons.mp hsplit.2.1).1 q hq
    have Hsk : Ω q p= -Ω p q:=by
      have hh:=hΩ (p+q)
      simp only [map_add,AddMonoidHom.add_apply,hΩ,zero_add,add_zero] at hh
      omega
    change (Ω q p:ℝ)<0
    rw [Hsk,Int.cast_neg]
    exact neg_neg_of_pos (by exact_mod_cast Hpq)
  let ga:=completedListProduct v Ω C a F
  let gb:=completedListProduct v Ω C b F
  have hA:=strict_list_product_through v Ω C a F (fun x=>0 < incomingCovector Ω p x)
    (fun x y hx hy=>by simpa only [map_add] using add_pos hx hy) N
    (fun q hq j hj m hm=>by
      by_contra hn
      exact hm (((H q (by simp [hq]) j hj m hn).eval (incomingCovector Ω p)).1.mpr (hbefore q hq)))
  have hB:=strict_list_product_through v Ω C b F (fun x=>incomingCovector Ω p x<0)
    (fun x y hx hy=>by simpa only [map_add] using add_neg hx hy) N
    (fun q hq j hj m hm=>by
      by_contra hn
      exact hm (((H q (by simp [hq]) j hj m hn).eval (incomingCovector Ω p)).2.2.mpr (hafter q hq)))
  have heq : ga.val*(F p).val*gb.val=(completedListProduct v Ω C (a++p::b) F).val:=by
    simp only [ga,gb,completedListProduct,List.map_append,List.prod_append,List.map_cons,List.prod_cons,mul_assoc]
  have ht:=chart_three_truncated_unique v Ω C (incomingCovector Ω p)
    (completedListProduct v Ω C (a++p::b) F) ga.val (F p).val gb.val N
    ga.property.1 (F p).property.1 gb.property.1 heq
    (fun j hj m hm=>not_not.mp (fun hh=>hm (hA j hj m hh)))
    (fun j hj m hm=>((H p (by simp) j hj m hm).eval (incomingCovector Ω p)).2.1.mpr
      (by change (Ω p p:ℝ)=0; rw [hΩ,Int.cast_zero]))
    (fun j hj m hm=>not_not.mp (fun hh=>hm (hB j hj m hh)))
  exact fun n hn=>(ht n hn).2.1

theorem joint_recovered_from_incoming (hΩ : ∀m,Ω m m=0)
    (l : List M) (F : CompletedPositive v Ω C) (N : ℕ)
    (V : AddSubmonoid M) (hF : ∀n,coeff n F.val∈supportedSubring v Ω V)
    (hcover : ∀n,0<n → n≤N → ∀m,HasRootDegree C n m → m∈V → ∃p∈l,OnPositiveRay p m)
    (hpair : l.Pairwise (fun a b=>0<Ω a b))
    (hRay : ∀p∈l,∀n,n+1≤N → ∀m,
      coeff (n+1) (chartZero v Ω C (incomingCovector Ω p) F).val m≠0 → OnPositiveRay p m) :
    ∀n≤N,coeff n F.val=coeff n (completedListProduct v Ω C l
      (fun p=>chartZero v Ω C (incomingCovector Ω p) F)).val := by
  let G:=completedListProduct v Ω C l (fun p=>chartZero v Ω C (incomingCovector Ω p) F)
  apply incoming_unique_through v Ω C hΩ F G N
  intro n hn
  by_cases hn0 : n=0
  · subst n; rw [incomingCoefficient_zero,incomingCoefficient_zero]
  apply Finsupp.ext
  intro m
  by_cases hmV : m∈V
  · rw [incomingCoefficient_apply,incomingCoefficient_apply]
    split_ifs with hm
    · obtain ⟨p,hp,hpm⟩:=hcover n (by omega) hn m hm hmV
      have hmid:=ordered_ray_middle v Ω C hΩ l
        (fun p=>chartZero v Ω C (incomingCovector Ω p) F) N hRay hpair p hp
      have Hlog:=FormalLog.log_coeff_congr
        (chartZero v Ω C (incomingCovector Ω p) F).val
        (chartZero v Ω C (incomingCovector Ω p) G).val n (fun j hj=>hmid j (hj.trans hn))
      have hF:=incoming_same_ray v Ω C hpm F
      have hG:=incoming_same_ray v Ω C hpm G
      rw [hF,hG] at Hlog
      exact congrArg (fun x : Torus v Ω=>x m) Hlog
    · rfl
  · rw [incoming_coefficient_supported v Ω C V F hF n m hmV,
      incoming_coefficient_supported v Ω C V G
        (completed_list_supported v Ω C l _ V
          (fun p _=>(chartThree_supported v Ω C (incomingCovector Ω p) V F hF).2.1)) n m hmV]

end
end ElementaryPositivity.QuantumTorus

end

end OAI
