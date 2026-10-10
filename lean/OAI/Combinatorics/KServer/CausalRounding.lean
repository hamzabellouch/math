import Mathlib
import OAI.Combinatorics.KServer.JointBudget
import OAI.Combinatorics.KServer.MetricService

namespace OAI

/-! Pushing the actual finite rounded law onto one fixed finite state space. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.TreeRounding
attribute [local instance] Classical.propDecidable Classical.decEq
variable {α S:Type} [Fintype S]

def Law.mass (L:Law α) (f:α→S) (s:S):ℝ:=L.avg (fun a=>if f a=s then 1 else 0)
omit [Fintype S] in
lemma Law.mass_nonneg (L:Law α) (f:α→S) (s:S):0≤ L.mass f s:=by
  unfold Law.mass Law.avg
  exact sum_nonneg (fun ω _=>mul_nonneg (L.nonneg ω) (by dsimp only; split_ifs <;> norm_num))
lemma Law.mass_sum (L:Law α) (f:α→S):(∑ s,L.mass f s)=1:=by
  unfold Law.mass Law.avg
  rw [sum_comm]
  simp only [←mul_sum,sum_ite_eq,mem_univ,ite_true,mul_one,L.total]
lemma Law.mass_average (L:Law α) (f:α→S) (g:S→ℝ):
    (∑ s,L.mass f s*g s)=L.avg (fun a=>g (f a)):=by
  unfold Law.mass Law.avg
  simp only [sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro ω _
  simp only [mul_assoc,mul_ite,one_mul,zero_mul,ite_mul,mul_zero,sum_ite_eq,mem_univ,ite_true]
omit [Fintype S] in
lemma Law.mass_support (L:Law α) (f:α→S) {s:S} (hs:0<L.mass f s):∃ ω,f (L.point ω)=s:=by
  by_contra hn
  have he:∀ ω,f (L.point ω)≠s:=by simpa only [not_exists] using hn
  have hh:L.mass f s=0:=by simp only [Law.mass,Law.avg,he,ite_false,mul_zero,sum_const_zero]
  rw [hh] at hs
  exact lt_irrefl _ hs

def Law.distribution (L:Law α) (f:α→S):FiniteDistribution S:=
  ⟨L.mass f,L.mass_nonneg f,L.mass_sum f⟩

omit [Fintype S] in
lemma Law.mass_left {T:Type} [Fintype T] (L:Law α) (f:α→S) (g:α→T) (s:S):
    (∑ z:T,L.mass (fun a=>(f a,g a)) (s,z))=L.mass f s:=by
  unfold Law.mass Law.avg
  rw [sum_comm]
  apply sum_congr rfl
  intro ω _
  rw [←mul_sum]
  congr 1
  by_cases h:f (L.point ω)=s
  · simp only [Prod.mk.injEq,h,true_and,ite_true,sum_ite_eq,mem_univ,ite_true]
  · simp only [Prod.mk.injEq,h,false_and,ite_false,sum_const_zero]

lemma Law.mass_right {T:Type} [Fintype T] (L:Law α) (f:α→S) (g:α→T) (z:T):
    (∑ s:S,L.mass (fun a=>(f a,g a)) (s,z))=L.mass g z:=by
  unfold Law.mass Law.avg
  rw [sum_comm]
  apply sum_congr rfl
  intro ω _
  rw [←mul_sum]
  congr 1
  by_cases h:g (L.point ω)=z
  · simp only [Prod.mk.injEq,h,and_true,ite_true,sum_ite_eq,mem_univ,ite_true]
  · simp only [Prod.mk.injEq,h,and_false,ite_false,sum_const_zero]
end KServer.TreeRounding

end


/-! Explicit causal finite-state implementation of a family of consecutive
couplings. Only the two prescribed marginals are supplied, not a cost conclusion. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.CausalCouplings
attribute [local instance] Classical.propDecidable Classical.decEq
variable {X S:Type} [Fintype S] [Nonempty S]

structure Family (X S:Type) [Fintype S] where
  marginal:List X→ S→ ℝ
  nonneg:∀ h s,0≤ marginal h s
  normalized:∀ h,∑ s,marginal h s=1
  joint:List X→ X→ S→ S→ ℝ
  joint_nonneg:∀ h r s z,0≤ joint h r s z
  left:∀ h r s,∑ z,joint h r s z=marginal h s
  right:∀ h r z,∑ s,joint h r s z=marginal (h++[r]) z

variable (F:Family X S)
def kernel (h:List X) (r:X) (s z:S):ℝ:=
  if 0<F.marginal h s then F.joint h r s z/F.marginal h s else if z=Classical.choice ‹Nonempty S› then 1 else 0

lemma kernel_nonneg (h:List X) (r:X) (s z:S):0≤ kernel F h r s z:=by
  unfold kernel
  split_ifs with hs hz
  · exact div_nonneg (F.joint_nonneg h r s z) hs.le
  · norm_num
  · norm_num
lemma kernel_sum (h:List X) (r:X) (s:S):(∑ z,kernel F h r s z)=1:=by
  unfold kernel
  by_cases hs:0<F.marginal h s
  · simp only [ite_eq_left hs,←sum_div,F.left,div_self hs.ne']
  · simp [hs]

lemma disintegration (h:List X) (r:X) (s z:S):F.marginal h s*kernel F h r s z=F.joint h r s z:=by
  by_cases hs:0<F.marginal h s
  · simp only [kernel,ite_eq_left hs]
    field_simp
  · have hz:F.marginal h s=0:=le_antisymm (le_of_not_gt hs) (F.nonneg h s)
    have hj:F.joint h r s z=0:=by
      apply le_antisymm _ (F.joint_nonneg h r s z)
      calc _≤ ∑ z,F.joint h r s z:=single_le_sum (fun z _=>F.joint_nonneg h r s z) (mem_univ z)
           _ = 0:=by rw [F.left,hz]
    rw [hz,hj,zero_mul]

lemma push (h:List X) (r:X) (z:S):(∑ s,F.marginal h s*kernel F h r s z)=F.marginal (h++[r]) z:=by
  simp only [disintegration,F.right]

variable {k:ℕ} [NeZero k]
def machine : HiddenMachine.Data k X S where
  initial:=F.marginal []
  initial_nonneg:=F.nonneg []
  initial_sum:=F.normalized []
  transition h r:=kernel F (h.map Prod.fst) r
  transition_nonneg h r:=kernel_nonneg F (h.map Prod.fst) r
  transition_sum h r:=kernel_sum F (h.map Prod.fst) r
  output _ _ _ _:=0
  nullOutput _ _:=0

lemma machine_transition (h:List (X×Fin k)) (r:X):
    (machine (k:=k) F).transition h r=kernel F (h.map Prod.fst) r:=rfl

variable [MetricSpace X] (start:Configuration k X) (V:List X→ S→ Configuration k X)
variable (hc:∀ h r s,∃ i,V (h++[r]) s i=r)

def cost (h:List X) (s:S):List X→ ℝ
  | []=>0
  | r::σ=>∑ z,kernel F h r s z*(matching (V h s) (V (h++[r]) z)+cost (h++[r]) z σ)

def transport (h:List X) (r:X):ℝ:=∑ s,∑ z,F.joint h r s z*matching (V h s) (V (h++[r]) z)

def pathCost (h:List X):List X→ ℝ
  | []=>0
  | r::σ=>transport F V h r+pathCost (h++[r]) σ

lemma virtual_eq (h:List (X×Fin k)) (s:S) (σ:List X):
    HiddenMachine.virtualCost (machine F) start V hc h s σ=cost F V (h.map Prod.fst) s σ:=by
  induction σ generalizing h s with
  | nil=>rfl
  | cons r σ ih=>
    simp only [HiddenMachine.virtualCost,cost,machine_transition]
    apply sum_congr rfl
    intro z _
    rw [ih]
    simp only [List.map_append,List.map_cons,List.map_nil]

omit [NeZero k] in
lemma mean_path (h:List X) (σ:List X):
    (∑ s,F.marginal h s*cost F V h s σ)=pathCost F V h σ:=by
  induction σ generalizing h with
  | nil=>simp [cost,pathCost]
  | cons r σ ih=>
    simp only [cost,pathCost,mul_sum,mul_add,←mul_assoc,disintegration,sum_add_distrib]
    congr 1
    rw [sum_comm]
    simp only [←sum_mul,F.right]
    exact ih (h++[r])

include hc in
lemma exists_policy:
    ∃ A:Policy k X,StronglyLazy start A ∧ ∀ σ:List X,
      expectedCost A start σ≤ (∑ s,F.marginal [] s*matching start (V [] s))+pathCost F V [] σ:=by
  obtain ⟨A,hA,hB⟩:=HiddenMachine.causal_random_lazy_simulation (machine F) start V hc
  refine ⟨A,hA,fun σ=>?_⟩
  have hh:=hB σ
  change expectedCost A start σ ≤ (∑ s,F.marginal [] s*matching start (V [] s))+
    ∑ s,F.marginal [] s*HiddenMachine.virtualCost (machine F) start V hc [] s σ at hh
  simpa only [virtual_eq,List.map_nil,mean_path] using hh
end KServer.CausalCouplings

end


/-! Sequential balanced count sampling on one fixed finite tree. The full
old marginal is retained at every request, so one causal machine works at all
horizons. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.TreeRounding
attribute [local instance] Classical.propDecidable Classical.decEq
variable {X:Type} {n k:ℕ} [NeZero n]
variable (T:Tree n) {τ:ℝ} (hτ:22≤τ) (w:Fin n→ℝ) (hw:∀ u,0≤w u)
  (hscale:∀ u,u≠0→w (T.parent u)=τ*w u)
  (q:List X→Fin n→ℝ) (hq:∀ h v,0≤q h v) (hp:∀ h v,0≤T.park (q h) v)
  (hr:∀ h,q h 0=(k:ℝ))

structure CountState (T:Tree n) (k:ℕ) (a:Fin n→ℝ) where
  law:Law (Counts n)
  valid:∀ ω,T.Valid a (law.point ω)
  root:∀ ω,(law.point ω).subtree 0=(k:ℤ)
  mean:T.Means a law

include hq hp hr in
lemma count_initial:Nonempty (CountState T k (q [])):=by
  obtain ⟨L,hL,hm⟩:=tree_initialization T (q []) (Int.natCast_nonneg k)
    (hq []) (hp []) (by exact_mod_cast hr [])
  exact ⟨⟨L,fun ω=>(hL ω).1,fun ω=>(hL ω).2,hm⟩⟩

def initialCount:CountState T k (q []):=Classical.choice (count_initial T q hq hp hr)

include hτ hw hscale hq hp hr in
lemma count_step_exists (h:List X) (x:X) (S:CountState T k (q h)):
    ∃ L:Law (PairState n),
      (∀ f:Counts n→ℝ,L.avg (fun s=>f s.old)=S.law.avg f) ∧
      (∀ ω,T.Valid (q h) (L.point ω).old ∧ T.Valid (q (h++[x])) (L.point ω).new ∧
        (L.point ω).new.subtree 0=(k:ℤ)) ∧
      T.Means (q (h++[x])) (L.map PairState.new) ∧
      L.avg (fun s=>∑ u,w (T.parent u)*|(s.new.subtree u:ℝ)-(s.old.subtree u:ℝ)|)≤
        132*(∑ u,w (T.parent u)*|q h u-q (h++[x]) u|):=by
  exact rounded_step T hτ w (q h) (q (h++[x])) hw hscale (Int.natCast_nonneg k)
    (by exact_mod_cast hr h) (by exact_mod_cast hr (h++[x])) (hq h) (hp h)
    (hq (h++[x])) (hp (h++[x])) S.law S.valid S.mean

def countStepLaw (h:List X) (x:X) (S:CountState T k (q h)):Law (PairState n):=
  Classical.choose (count_step_exists T hτ w hw hscale q hq hp hr h x S)

theorem countStep_spec (h:List X) (x:X) (S:CountState T k (q h)) :
    (∀ f:Counts n→ℝ,(countStepLaw T hτ w hw hscale q hq hp hr h x S).avg (fun s=>f s.old)=S.law.avg f) ∧
    (∀ ω,T.Valid (q h) ((countStepLaw T hτ w hw hscale q hq hp hr h x S).point ω).old ∧
      T.Valid (q (h++[x])) ((countStepLaw T hτ w hw hscale q hq hp hr h x S).point ω).new ∧
      ((countStepLaw T hτ w hw hscale q hq hp hr h x S).point ω).new.subtree 0=(k:ℤ)) ∧
    T.Means (q (h++[x])) ((countStepLaw T hτ w hw hscale q hq hp hr h x S).map PairState.new) ∧
    (countStepLaw T hτ w hw hscale q hq hp hr h x S).avg
      (fun s=>∑ u,w (T.parent u)*|(s.new.subtree u:ℝ)-(s.old.subtree u:ℝ)|)≤
        132*(∑ u,w (T.parent u)*|q h u-q (h++[x]) u|) :=
  Classical.choose_spec (count_step_exists T hτ w hw hscale q hq hp hr h x S)

def nextCount (h:List X) (x:X) (S:CountState T k (q h)):CountState T k (q (h++[x])) where
  law:=(countStepLaw T hτ w hw hscale q hq hp hr h x S).map PairState.new
  valid ω:=(countStep_spec T hτ w hw hscale q hq hp hr h x S).2.1 ω |>.2.1
  root ω:=(countStep_spec T hτ w hw hscale q hq hp hr h x S).2.1 ω |>.2.2
  mean:=(countStep_spec T hτ w hw hscale q hq hp hr h x S).2.2.1

def countState (h:List X):CountState T k (q h):=
  List.reverseRecOn h (initialCount T q hq hp hr)
    (fun h x S=>nextCount T hτ w hw hscale q hq hp hr h x S)

lemma countState_nil:countState T hτ w hw hscale q hq hp hr []=initialCount T q hq hp hr:=by
  simp only [countState,List.reverseRecOn_nil]
lemma countState_snoc (h:List X) (x:X):
    countState T hτ w hw hscale q hq hp hr (h++[x])=
      nextCount T hτ w hw hscale q hq hp hr h x (countState T hτ w hw hscale q hq hp hr h):=by
  simp only [countState,List.reverseRecOn_concat]

def pairLaw (h:List X) (x:X):Law (PairState n):=
  countStepLaw T hτ w hw hscale q hq hp hr h x (countState T hτ w hw hscale q hq hp hr h)

def countFamily:CausalCouplings.Family X (Inventory T k) where
  marginal h:=(countState T hτ w hw hscale q hq hp hr h).law.mass (pack T)
  nonneg h:=(countState T hτ w hw hscale q hq hp hr h).law.mass_nonneg (pack T)
  normalized h:=(countState T hτ w hw hscale q hq hp hr h).law.mass_sum (pack T)
  joint h x s z:=(pairLaw T hτ w hw hscale q hq hp hr h x).mass
    (fun p=>(pack T p.old,pack T p.new)) (s,z)
  joint_nonneg h x s z:=(pairLaw T hτ w hw hscale q hq hp hr h x).mass_nonneg _ _
  left h x s:=by
    rw [Law.mass_left]
    unfold Law.mass pairLaw countStepLaw
    exact (countStep_spec T hτ w hw hscale q hq hp hr h x
      (countState T hτ w hw hscale q hq hp hr h)).1 (fun c=>@ite ℝ (pack T c=s) (Classical.decEq _ _ _) 1 0)
  right h x z:=by
    rw [Law.mass_right,countState_snoc]
    rfl

end KServer.TreeRounding

end


/-! The sequential family keeps exact new park means and the factor-132
weighted subtree transport estimate. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.TreeRounding
attribute [local instance] Classical.propDecidable Classical.decEq
variable {X:Type} {n k:ℕ} [NeZero n]
variable (T:Tree n) {τ:ℝ} (hτ:22≤τ) (w:Fin n→ℝ) (hw:∀ u,0≤w u)
  (hscale:∀ u,u≠0→w (T.parent u)=τ*w u)
  (q:List X→Fin n→ℝ) (hq:∀ h v,0≤q h v) (hp:∀ h v,0≤T.park (q h) v)
  (hr:∀ h,q h 0=(k:ℝ))

lemma marginal_valid (h:List X) (c:Inventory T k)
    (hc:0<(countFamily T hτ w hw hscale q hq hp hr).marginal h c):T.Valid (q h) c.val:=by
  obtain ⟨ω,he⟩:=(countState T hτ w hw hscale q hq hp hr h).law.mass_support (pack T) hc
  rw [←he,pack_val T _ (good_of_valid T _ (hr h) _ ((countState T hτ w hw hscale q hq hp hr h).valid ω))]
  exact (countState T hτ w hw hscale q hq hp hr h).valid ω

lemma pair_old_valid (h:List X) (x:X) (ω:(pairLaw T hτ w hw hscale q hq hp hr h x).Ω):
    T.Valid (q h) ((pairLaw T hτ w hw hscale q hq hp hr h x).point ω).old:=
  (countStep_spec T hτ w hw hscale q hq hp hr h x (countState T hτ w hw hscale q hq hp hr h)).2.1 ω |>.1
lemma pair_new_valid (h:List X) (x:X) (ω:(pairLaw T hτ w hw hscale q hq hp hr h x).Ω):
    T.Valid (q (h++[x])) ((pairLaw T hτ w hw hscale q hq hp hr h x).point ω).new:=
  (countStep_spec T hτ w hw hscale q hq hp hr h x (countState T hτ w hw hscale q hq hp hr h)).2.1 ω |>.2.1

lemma joint_average (h:List X) (x:X) (g:Inventory T k→Inventory T k→ℝ):
    (∑ c,∑ e,(countFamily T hτ w hw hscale q hq hp hr).joint h x c e*g c e)=
      (pairLaw T hτ w hw hscale q hq hp hr h x).avg (fun p=>g (pack T p.old) (pack T p.new)):=by
  exact (Fintype.sum_prod_type _).symm.trans
    ((pairLaw T hτ w hw hscale q hq hp hr h x).mass_average (fun p=>(pack T p.old,pack T p.new)) (fun p=>g p.1 p.2))

lemma expected_bound (h:List X) (x:X) (g:Inventory T k→Inventory T k→ℝ) (m:Fin n→ℝ)
    {a b:ℝ} (ha:0≤a)
    (hg:∀ c e:Inventory T k,T.Valid (q h) c.val→T.Valid (q (h++[x])) e.val→
      g c e≤a*(∑ u,w (T.parent u)*|(c.val.subtree u:ℝ)-(e.val.subtree u:ℝ)|)+
        b*(∑ u,(e.val.park u:ℝ)*m u)):
    (∑ c,∑ e,(countFamily T hτ w hw hscale q hq hp hr).joint h x c e*g c e)≤
      a*132*(∑ u,w (T.parent u)*|q h u-q (h++[x]) u|)+b*(∑ u,T.park (q (h++[x])) u*m u):=by
  rw [joint_average]
  let P:=pairLaw T hτ w hw hscale q hq hp hr h x
  have hbound:P.avg (fun p=>g (pack T p.old) (pack T p.new))≤
      P.avg (fun p=>a*(∑ u,w (T.parent u)*|(p.new.subtree u:ℝ)-(p.old.subtree u:ℝ)|)+
        b*(∑ u,(p.new.park u:ℝ)*m u)):=by
    apply Law.avg_le_of_support
    intro ω
    have ho:=pair_old_valid T hτ w hw hscale q hq hp hr h x ω
    have hn:=pair_new_valid T hτ w hw hscale q hq hp hr h x ω
    have hgo:=good_of_valid T _ (hr h) _ ho
    have hgn:=good_of_valid T _ (hr (h++[x])) _ hn
    have hh:=hg (pack T (P.point ω).old) (pack T (P.point ω).new)
      (by rwa [pack_val T _ hgo]) (by rwa [pack_val T _ hgn])
    have heo:(pack T (P.point ω).old:Inventory T k).val=(P.point ω).old:=pack_val T _ hgo
    have hen:(pack T (P.point ω).new:Inventory T k).val=(P.point ω).new:=pack_val T _ hgn
    rw [heo,hen] at hh
    simpa only [abs_sub_comm] using hh
  have hmean:(P.map PairState.new).avg (fun c=>∑ u,(c.park u:ℝ)*m u)=
      ∑ u,T.park (q (h++[x])) u*m u:=by
    rw [Law.avg_sum]
    apply sum_congr rfl
    intro u _
    have hh:=(countStep_spec T hτ w hw hscale q hq hp hr h x
      (countState T hτ w hw hscale q hq hp hr h)).2.2.1.2 u
    change (P.map PairState.new).avg (fun c=>(c.park u:ℝ))=T.park (q (h++[x])) u at hh
    calc
      _=m u*(P.map PairState.new).avg (fun c=>(c.park u:ℝ)):=by
        simpa only [mul_comm] using (P.map PairState.new).avg_mul (m u) (fun c=>(c.park u:ℝ))
      _=T.park (q (h++[x])) u*m u:=by rw [hh,mul_comm]
  have hm:= (countStep_spec T hτ w hw hscale q hq hp hr h x
      (countState T hτ w hw hscale q hq hp hr h)).2.2.2
  rw [Law.avg_add,Law.avg_mul,Law.avg_mul] at hbound
  rw [Law.map_avg] at hmean
  change P.avg (fun p=>∑ u,(p.new.park u:ℝ)*m u)=_ at hmean
  rw [hmean] at hbound
  exact hbound.trans (by simpa only [P,pairLaw,mul_assoc,add_comm] using add_le_add_right (mul_le_mul_of_nonneg_left hm ha) (b*∑ u,T.park (q (h++[x])) u*m u))
end KServer.TreeRounding

end


/-! An independent permanent finite tape, sampled once before the requests. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.CausalCouplings
attribute [local instance] Classical.propDecidable Classical.decEq
variable {X I S:Type} [Fintype I] [Fintype S]
variable (w:I→ℝ) (hw:∀ i,0≤w i) (h1:∑ i,w i=1) (F:I→Family X S)

def mixture:Family X (I×S) where
  marginal h s:=w s.1*(F s.1).marginal h s.2
  nonneg h s:=mul_nonneg (hw s.1) ((F s.1).nonneg h s.2)
  normalized h:=by simp only [Fintype.sum_prod_type,←mul_sum,Family.normalized,mul_one,h1]
  joint h r s z:=if s.1=z.1 then w s.1*(F s.1).joint h r s.2 z.2 else 0
  joint_nonneg h r s z:=by split_ifs; exact mul_nonneg (hw _) ((F _).joint_nonneg _ _ _ _); rfl
  left h r s:=by
    simp only [Fintype.sum_prod_type]
    rw [sum_eq_single s.1]
    · simp only [ite_true,←mul_sum,Family.left]
    · intro i _ hi
      simp only [Ne.symm hi,ite_false,sum_const_zero]
    · simp only [mem_univ,not_true_eq_false,false_implies]
  right h r z:=by
    simp only [Fintype.sum_prod_type]
    rw [sum_eq_single z.1]
    · simp only [ite_true,←mul_sum,Family.right]
    · intro i _ hi
      simp only [hi,ite_false,sum_const_zero]
    · simp only [mem_univ,not_true_eq_false,false_implies]

lemma mixture_transport [MetricSpace X] {k:ℕ} (V:I→List X→S→ Configuration k X) (h:List X) (r:X):
    transport (mixture w hw h1 F) (fun h s=>V s.1 h s.2) h r=
      ∑ i,w i*transport (F i) (V i) h r:=by
  unfold transport mixture
  simp only [Fintype.sum_prod_type]
  apply sum_congr rfl
  intro i _
  rw [mul_sum]
  apply sum_congr rfl
  intro s _
  rw [sum_eq_single i]
  · simp only [ite_true,mul_assoc,mul_sum]
  · intro j _ hj
    simp only [Ne.symm hj,ite_false,zero_mul,sum_const_zero]
  · simp only [mem_univ,not_true_eq_false,false_implies]

lemma mixture_path [MetricSpace X] {k:ℕ} (V:I→List X→S→ Configuration k X) (h σ:List X):
    pathCost (mixture w hw h1 F) (fun h s=>V s.1 h s.2) h σ=
      ∑ i,w i*pathCost (F i) (V i) h σ:=by
  induction σ generalizing h with
  | nil=>simp only [pathCost,mul_zero,sum_const_zero]
  | cons r σ ih=>simp only [pathCost,mixture_transport,ih,mul_add,sum_add_distrib]

variable [Nonempty S] [MetricSpace X] {k:ℕ} [NeZero k]

def safeConfig (z:X) (V:List X→S→ Configuration k X) (h:List X) (s:S):Configuration k X:=
  if h=[] then V h s else if ∃ i,V h s i=h.getLastD z then V h s else fun _=>h.getLastD z

omit [Fintype S] [Nonempty S] [MetricSpace X] in
lemma safeConfig_serves (z:X) (V:List X→S→ Configuration k X) (h:List X) (r:X) (s:S):
    ∃ i,safeConfig z V (h++[r]) s i=r:=by
  have hn:h++[r]≠[]:=by simp
  have he:(h++[r]).getLastD z=r:=by simp
  unfold safeConfig
  rw [ite_eq_right hn,he]
  split_ifs with hs
  · exact hs
  · exact ⟨0,rfl⟩

omit [Fintype S] [Nonempty S] [MetricSpace X] [NeZero k] in
lemma safeConfig_eq_nil (z:X) (V:List X→S→ Configuration k X) (s:S):
    safeConfig z V [] s=V [] s:=by simp only [safeConfig,ite_true]

omit [Fintype S] [Nonempty S] [MetricSpace X] [NeZero k] in
lemma safeConfig_eq (z:X) (V:List X→S→ Configuration k X) (h:List X) (s:S)
    (hc:∃ i,V h s i=h.getLastD z):safeConfig z V h s=V h s:=by
  unfold safeConfig
  split_ifs <;> rfl
end KServer.CausalCouplings

end


/-! Explicit finite-horizon cost of the same causal machine. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.CausalCouplings
variable {X S:Type} [Fintype S] [Nonempty S] [MetricSpace X] {k:ℕ}

omit [Nonempty S] in
lemma path_ofFn (F:Family X S) (V:List X→ S→ Configuration k X) (h:List X)
    {H:ℕ} (σ:Fin H→X):
    pathCost F V h (List.ofFn σ)=∑ t:Fin H,transport F V (h++(List.ofFn σ).take t.val) (σ t):=by
  induction H generalizing h with
  | zero=>simp only [List.ofFn_zero,pathCost,Fin.sum_univ_zero]
  | succ H ih=>
    rw [List.ofFn_succ,pathCost,ih,Fin.sum_univ_succ]
    simp only [Fin.val_zero,List.take_zero,List.append_nil,Fin.val_succ,List.take_succ_cons]
    congr 1
    apply sum_congr rfl
    intro t _
    congr 1
    simp only [List.append_assoc,List.singleton_append]
end KServer.CausalCouplings

end


/-! Actual history-indexed count laws and their rendered labeled configurations.
Impossible histories are completed by a service-safe output, whereas every
positive experimental prefix uses the genuine allocated occupied anchors. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.JointRounded
open JointExperiment JointAllocation JointHistory CausalCouplings
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Y:Type} [MetricSpace Y] [Fintype Y] {k H L:ℕ} [NeZero k]
variable (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
variable {r:Fin L→ℝ} (hr:∀ d,0<r d) (hk:1≤(k:ℝ))

abbrev T:=PrefixTree.tree (LevelKeys.Key Y k) L
abbrev State:=TreeRounding.Inventory (T (Y:=Y) (k:=k) (L:=L)) k

def family {R τ:ℝ} (hR:0≤R) (hτ:22≤τ) (tape:Tape Y k H L r):Family Y (State (Y:=Y) (k:=k) (L:=L)):=
  TreeRounding.countFamily T hτ (PrefixTree.weight (LevelKeys.Key Y k) L R τ)
    (PrefixTree.weight_nonneg _ L hR (by linarith)) (PrefixTree.parent_weight _ L (by linarith))
    (q s law hr hk tape) (q_nonneg s law hr hk tape) (q_park_nonneg s law hr hk tape) (q_root s law hr hk tape)

def rawConfig (tape:Tape Y k H L r) (h:List Y) (c:State (Y:=Y) (k:=k) (L:=L)):Configuration k Y:=
  PrefixTree.countConfig (LevelKeys.Key Y k) L (s 0) (a s law hr tape h) c

def config (tape:Tape Y k H L r):List Y→ State (Y:=Y) (k:=k) (L:=L)→ Configuration k Y:=
  safeConfig (s 0) (rawConfig s law hr tape)

lemma config_serves (tape:Tape Y k H L r) (h:List Y) (x:Y) (c:State (Y:=Y) (k:=k) (L:=L)):
    ∃ i,config s law hr tape (h++[x]) c i=x:=safeConfig_serves _ _ _ _ _

lemma q_take (t:ℕ) (ht:t≤H) (ω:Atom (k:=k) law hr):
    q s law hr hk ω.val.2 ((List.ofFn ω.val.1).take t)=quota s law hr hk t ω:=by
  rw [q_eq s law hr hk _ _ ω (observed_true law hr ω t ht)]
  simp only [List.length_take,List.length_ofFn,Nat.min_eq_left ht]
lemma a_take (t:ℕ) (ht:t≤H) (ω:Atom (k:=k) law hr):
    a s law hr ω.val.2 ((List.ofFn ω.val.1).take t)=anchors s law hr t ω:=by
  rw [a_eq s law hr _ _ ω (observed_true law hr ω t ht)]
  simp only [List.length_take,List.length_ofFn,Nat.min_eq_left ht]

omit [MetricSpace Y] [Fintype Y] in
lemma take_succ (t:Fin H) (σ:Fin H→Y):
    (List.ofFn σ).take (t.val+1)=(List.ofFn σ).take t.val++[σ t]:=by
  rw [List.take_succ_eq_append_getElem (by simpa only [List.length_ofFn] using t.isLt)]
  rw [List.getElem_ofFn]


lemma raw_take (t:ℕ) (ht:t≤H) (ω:Atom (k:=k) law hr) (c:State (Y:=Y) (k:=k) (L:=L)):
    rawConfig s law hr ω.val.2 ((List.ofFn ω.val.1).take t) c=
      PrefixTree.countConfig _ L (s 0) (anchors s law hr t ω) c:=by
  unfold rawConfig
  rw [a_take s law hr t ht ω]

lemma config_take (hL:0<L) (hf:∀ x y:Y,dist x y≤20*r ⟨L-1,by omega⟩→x=y)
    (t:ℕ) (ht:t≤H) (ω:Atom (k:=k) law hr) (c:State (Y:=Y) (k:=k) (L:=L))
    (hc:T.Valid (quota s law hr hk t ω) c.val):
    config s law hr ω.val.2 ((List.ofFn ω.val.1).take t) c=
      PrefixTree.countConfig _ L (s 0) (anchors s law hr t ω) c:=by
  unfold config
  have he:safeConfig (s 0) (rawConfig s law hr ω.val.2) ((List.ofFn ω.val.1).take t) c=
      rawConfig s law hr ω.val.2 ((List.ofFn ω.val.1).take t) c:=by
    cases t with
    | zero=>simp only [List.take_zero,safeConfig_eq_nil]
    | succ t=>
      apply safeConfig_eq
      obtain ⟨i,hi⟩:=JointService.count_serves s law hr hk hL hf ⟨t,by omega⟩ ω c hc
      refine ⟨i,?_⟩
      rw [raw_take s law hr (t+1) ht ω c,hi,take_succ ⟨t,by omega⟩]
      simp only [List.getLastD_concat]
  rw [he]
  exact raw_take s law hr t ht ω c

lemma step_bound {R τ:ℝ} (hR:0≤R) (hτ:22≤τ) (hdia:∀ x y:Y,dist x y≤R)
    (hrad:∀ d,r d=R/τ^(d.val+1)) (hL:0<L)
    (hf:∀ x y:Y,dist x y≤20*r ⟨L-1,by omega⟩→x=y)
    (t:Fin H) (ω:Atom (k:=k) law hr):
    transport (family s law hr hk hR hτ ω.val.2) (config s law hr ω.val.2)
      ((List.ofFn ω.val.1).take t.val) (ω.val.1 t)≤
      15840*JointBudget.stepQuota s law hr hk R τ t.val ω+40*JointHeavy.travel s law hr hk t.val ω:=by
  have hold:=q_take s law hr hk t.val (Nat.le_of_lt t.isLt) ω
  have hnew:q s law hr hk ω.val.2 ((List.ofFn ω.val.1).take t.val++[ω.val.1 t])=
      quota s law hr hk (t.val+1) ω:=by
    rw [←take_succ t ω.val.1]
    exact q_take s law hr hk _ (by omega) ω
  have hh:=TreeRounding.expected_bound T hτ (PrefixTree.weight (LevelKeys.Key Y k) L R τ)
    (PrefixTree.weight_nonneg _ L hR (by linarith)) (PrefixTree.parent_weight _ L (by linarith))
    (q s law hr hk ω.val.2) (q_nonneg s law hr hk ω.val.2) (q_park_nonneg s law hr hk ω.val.2)
    (q_root s law hr hk ω.val.2) ((List.ofFn ω.val.1).take t.val) (ω.val.1 t)
    (fun c e=>matching (config s law hr ω.val.2 ((List.ofFn ω.val.1).take t.val) c)
      (config s law hr ω.val.2 ((List.ofFn ω.val.1).take t.val++[ω.val.1 t]) e))
    (PrefixTree.nodeMotion _ L (JointMetric.motion s law hr t.val ω)) (a:=120) (b:=40) (by norm_num)
    (fun c e hc he=>by
      rw [hold] at hc
      rw [hnew] at he
      rw [←take_succ t ω.val.1,config_take s law hr hk hL hf _ (by omega) ω c hc,
        config_take s law hr hk hL hf _ (by omega) ω e he]
      exact JointMetric.count_matching s law hr hk hR (by linarith) hdia hrad t ω c e hc he)
  change transport (family s law hr hk hR hτ ω.val.2) (config s law hr ω.val.2) _ _≤_ at hh
  rw [hold,hnew] at hh
  have hm:(∑ v,T.park (quota s law hr hk (t.val+1) ω) v*
      PrefixTree.nodeMotion _ L (JointMetric.motion s law hr t.val ω) v)=JointHeavy.travel s law hr hk t.val ω:=
    JointMetric.motion_sum s law hr hk t.val ω
  rw [hm] at hh
  simpa only [JointBudget.stepQuota,abs_sub_comm,show (120:ℝ)*132=15840 by norm_num] using hh
end KServer.JointRounded

end


/-! The actual permanent-tape sequentially rounded experiment returns a causal
strongly lazy policy. All impossible histories were already service-completed. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.JointPolicy
open JointExperiment JointRounded CausalCouplings RankTracking ActualCharges
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Y:Type} [MetricSpace Y] [Fintype Y] {k H L:ℕ} [NeZero k]
variable (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
variable {r:Fin L→ℝ} (hr:∀ d,0<r d) (hk:1≤(k:ℝ))

omit [NeZero k] in
include hr in
lemma tape_nonempty : Nonempty (Tape Y k H L r):=by
  by_contra h
  have : IsEmpty (Tape Y k H L r):=not_nonempty_iff.mp h
  have hh:=tapeWeight_sum (Y:=Y) (k:=k) (H:=H) hr
  simp only [sum_of_isEmpty,zero_ne_one] at hh

abbrev MixState:=Tape Y k H L r × State (Y:=Y) (k:=k) (L:=L)

def mixed {R τ:ℝ} (hR:0≤R) (hτ:22≤τ):Family Y (MixState (Y:=Y) (k:=k) (H:=H) (r:=r)):=
  mixture (tapeWeight r) (tapeWeight_nonneg hr) (tapeWeight_sum hr) (family s law hr hk hR hτ)

def rendered (h:List Y) (z:MixState (Y:=Y) (k:=k) (H:=H) (r:=r)):Configuration k Y:=
  config s law hr z.1 h z.2

lemma rendered_serves (h:List Y) (x:Y) (z:MixState (Y:=Y) (k:=k) (H:=H) (r:=r)):
    ∃ i,rendered s law hr (h++[x]) z i=x:=
  safeConfig_serves (s 0) (rawConfig s law hr z.1) h x z.2

lemma mean_path {R τ:ℝ} (hR:0≤R) (hτ:22≤τ):
    (∑ σ,law.val σ*pathCost (mixed s law hr hk hR hτ) (rendered s law hr) [] (List.ofFn σ))=
      ∑ t:Fin H,avg (weight law hr) (fun ω=>
        transport (family s law hr hk hR hτ ω.val.2) (config s law hr ω.val.2)
          ((List.ofFn ω.val.1).take t.val) (ω.val.1 t)):=by
  have := tape_nonempty (Y:=Y) (k:=k) (H:=H) hr
  simp_rw [path_ofFn,List.nil_append]
  unfold mixed rendered
  simp_rw [mixture_transport]
  have hav (t:Fin H):avg (weight law hr) (fun ω=>
        transport (family s law hr hk hR hτ ω.val.2) (config s law hr ω.val.2)
          ((List.ofFn ω.val.1).take t.val) (ω.val.1 t))=
      ∑ σ,law.val σ*(∑ a:Tape Y k H L r,tapeWeight r a*
        transport (family s law hr hk hR hτ a) (config s law hr a)
          ((List.ofFn σ).take t.val) (σ t)):=by
    rw [avg_raw law hr (fun z:Raw Y k H L r =>
      transport (family s law hr hk hR hτ z.2) (config s law hr z.2)
        ((List.ofFn z.1).take t.val) (z.1 t))]
    simp only [avg,rawWeight,FiniteExperiment.weight,tapeLaw,Fintype.sum_prod_type,mul_sum,mul_assoc]
  simp_rw [hav,mul_sum]
  rw [sum_comm]

lemma path_bound {R τ:ℝ} (hR:0≤R) (hτ:22≤τ) (hdia:∀ x y:Y,dist x y≤R)
    (hrad:∀ d,r d=R/τ^(d.val+1)) (hL:0<L)
    (hf:∀ x y:Y,dist x y≤20*r ⟨L-1,by omega⟩→x=y):
    (∑ σ,law.val σ*pathCost (mixed s law hr hk hR hτ) (rendered s law hr) [] (List.ofFn σ))≤
      15840*total (weight law hr) H (JointBudget.stepQuota s law hr hk R τ)+
        40*total (weight law hr) H (JointHeavy.travel s law hr hk):=by
  rw [mean_path]
  have hb:=sum_le_sum (s:=univ) (fun t (_:t∈univ)=>
    avg_mono (weight_nonneg law hr) (fun ω=>step_bound s law hr hk hR hτ hdia hrad hL hf t ω))
  simp only [avg_add,avg_mul,sum_add_distrib,←mul_sum] at hb
  unfold total
  rw [←Fin.sum_univ_eq_sum_range (fun t=>avg (weight law hr) (JointBudget.stepQuota s law hr hk R τ t)) H,
    ←Fin.sum_univ_eq_sum_range (fun t=>avg (weight law hr) (JointHeavy.travel s law hr hk t)) H]
  exact hb

lemma exists_policy {R τ:ℝ} (hR:0≤R) (hτ:22≤τ) (hdia:∀ x y:Y,dist x y≤R)
    (hrad:∀ d,r d=R/τ^(d.val+1)) (hL:0<L)
    (hf:∀ x y:Y,dist x y≤20*r ⟨L-1,by omega⟩→x=y):
    ∃ A:Policy k Y,StronglyLazy s A ∧
      (∑ σ,law.val σ*expectedCost A s (List.ofFn σ))≤
        15840*total (weight law hr) H (JointBudget.stepQuota s law hr hk R τ)+
        40*total (weight law hr) H (JointHeavy.travel s law hr hk)+(k:ℝ)*R:=by
  have := tape_nonempty (Y:=Y) (k:=k) (H:=H) hr
  obtain ⟨A,hA,hcost⟩:=CausalCouplings.exists_policy (mixed s law hr hk hR hτ) s
    (rendered s law hr) (rendered_serves s law hr)
  refine ⟨A,hA,?_⟩
  have hi:(∑ z,(mixed s law hr hk hR hτ).marginal [] z*matching s (rendered s law hr [] z))≤(k:ℝ)*R:=by
    have hh:=sum_le_sum (s:=univ) (fun z (_:z∈univ)=>mul_le_mul_of_nonneg_left
      (Episode.matching_le_diameter s (rendered s law hr [] z) R hdia)
      ((mixed s law hr hk hR hτ).nonneg [] z))
    simpa only [←sum_mul,Family.normalized,one_mul] using hh
  have he:=sum_le_sum (s:=univ) (fun σ (_:σ∈univ)=>mul_le_mul_of_nonneg_left (hcost (List.ofFn σ)) (law.property.1 σ))
  simp only [mul_add,sum_add_distrib,←sum_mul,law.property.2,one_mul] at he
  have hp:=path_bound s law hr hk hR hτ hdia hrad hL hf
  linarith
end KServer.JointPolicy

end

end OAI
