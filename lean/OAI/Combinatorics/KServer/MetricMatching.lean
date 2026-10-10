import Mathlib
import OAI.Combinatorics.KServer.PrefixAllocation

namespace OAI

/-! In a finite laminar tree, one matching simultaneously has the optimal
crossing count at every cut. This is proved by the uncrossing minimizer, rather
than assuming a transport/matching interface. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.LaminarMatching
attribute [local instance] Classical.propDecidable Classical.decEq
variable {V Z I:Type*} [Fintype V] [Fintype I]

def Laminar (c:V→Z→Bool):Prop:=∀ v w,
  (∀ z,c v z=true→c w z=true) ∨ (∀ z,c w z=true→c v z=true) ∨
    (∀ z,c v z=true→c w z=false)

def bit (b:Bool):ℝ:=if b then 1 else 0

def cross (c:V→Z→Bool) (f g:I→Z) (π:Equiv.Perm I) (v:V) (i:I):ℝ:=
  |bit (c v (f i))-bit (c v (g (π i)))|

def cost (c:V→Z→Bool) (f g:I→Z) (π:Equiv.Perm I):ℝ:=∑ v,∑ i,cross c f g π v i

lemma pair_inequality (a b c d:Bool) (h:a=d ∨ c=b):
    |bit a-bit d|+|bit c-bit b|≤|bit a-bit b|+|bit c-bit d|:=by
  cases a <;> cases b <;> cases c <;> cases d <;> norm_num [bit] at *

omit [Fintype V] in
lemma laminar_pair {c:V→Z→Bool} (hc:Laminar c) (v w:V) {a b d e:Z}
    (ha:c v a=true) (hb:c v b=false) (hd:c v d=false) (he:c v e=true):
    c w a=c w e ∨ c w d=c w b:=by
  rcases hc v w with h|h|h
  · exact Or.inl ((h a ha).trans (h e he).symm)
  · right
    have hb':c w b=false:=by cases hcb:c w b; rfl; have :=h b hcb; simp [hb] at this
    have hd':c w d=false:=by cases hcd:c w d; rfl; have :=h d hcd; simp [hd] at this
    exact hd'.trans hb'.symm
  · exact Or.inl ((h a ha).trans (h e he).symm)

lemma two_term_sum {f g:I→ℝ} {i j:I} (hij:i≠j)
    (h:∀ x,x≠i→x≠j→f x=g x):
    (∑ x,f x)-(∑ x,g x)=(f i+f j)-(g i+g j):=by
  rw [←sum_sub_distrib]
  have hh:(∑ x,(f x-g x))=(f i-g i)+(f j-g j):=by
    rw [←add_sum_erase univ _ (mem_univ i)]
    rw [←add_sum_erase (univ.erase i) _ (mem_erase.mpr ⟨Ne.symm hij,mem_univ j⟩)]
    have hz:(∑ x∈(univ.erase i).erase j,(f x-g x))=0:=by
      apply sum_eq_zero
      intro x hx
      rw [h x (mem_erase.mp (mem_erase.mp hx).2).1 (mem_erase.mp hx).1,sub_self]
    rw [hz,add_zero]
  rw [hh]
  ring

omit [Fintype V] in
lemma swapped_cuts {c:V→Z→Bool} (hc:Laminar c) (f g:I→Z) (π:Equiv.Perm I) (v:V) (i j:I)
    (ha:c v (f i)=true) (hb:c v (g (π i))=false)
    (hd:c v (f j)=false) (he:c v (g (π j))=true):
    ∀ w,(∑ x,cross c f g ((Equiv.swap i j).trans π) w x)≤∑ x,cross c f g π w x:=by
  have hij:i≠j:=by intro hij; subst j; simp [ha] at hd
  intro w
  have hsum:=two_term_sum (f:=cross c f g ((Equiv.swap i j).trans π) w)
    (g:=cross c f g π w) hij (fun x hxi hxj=>by
      simp only [cross,Equiv.trans_apply,Equiv.swap_apply_of_ne_of_ne hxi hxj])
  have hh:=pair_inequality (c w (f i)) (c w (g (π i))) (c w (f j)) (c w (g (π j)))
    (laminar_pair hc v w ha hb hd he)
  simp only [cross,Equiv.trans_apply,Equiv.swap_apply_left,Equiv.swap_apply_right] at hsum
  simp only [cross,Equiv.trans_apply]
  linarith

lemma swapped_strict {c:V→Z→Bool} (hc:Laminar c) (f g:I→Z) (π:Equiv.Perm I) (v:V) (i j:I)
    (ha:c v (f i)=true) (hb:c v (g (π i))=false)
    (hd:c v (f j)=false) (he:c v (g (π j))=true):
    cost c f g ((Equiv.swap i j).trans π)<cost c f g π:=by
  apply sum_lt_sum (fun w _=>swapped_cuts hc f g π v i j ha hb hd he w)
  refine ⟨v,mem_univ _,?_⟩
  have hij:i≠j:=by intro hij; subst j; simp [ha] at hd
  have hsum:=two_term_sum (f:=cross c f g ((Equiv.swap i j).trans π) v)
    (g:=cross c f g π v) hij (fun x hxi hxj=>by
      simp only [cross,Equiv.trans_apply,Equiv.swap_apply_of_ne_of_ne hxi hxj])
  norm_num [cross,Equiv.trans_apply,ha,hb,hd,he,bit] at hsum
  simp only [cross,Equiv.trans_apply,bit]
  linarith

lemma bit_lt {a b:Bool} (h:bit a<bit b):a=false ∧ b=true:=by
  cases a <;> cases b <;> norm_num [bit] at *

/-- An optimal permutation has no opposite crossings at any cut. -/
lemma minimizing_oriented {c:V→Z→Bool} (hc:Laminar c) (f g:I→Z) (π:Equiv.Perm I)
    (hm:∀ ρ,cost c f g π≤cost c f g ρ) (v:V):
    (∀ i,bit (c v (f i))≤bit (c v (g (π i)))) ∨
      (∀ i,bit (c v (g (π i)))≤bit (c v (f i))):=by
  by_cases h:∀ i,bit (c v (f i))≤bit (c v (g (π i)))
  · exact Or.inl h
  · right
    push Not at h
    obtain ⟨i,hi⟩:=h
    obtain ⟨hb,ha⟩:=bit_lt hi
    intro j
    by_contra hj
    obtain ⟨hd,he⟩:=bit_lt (lt_of_not_ge hj)
    exact (not_lt_of_ge (hm _)) (swapped_strict hc f g π v i j ha hb hd he)

omit [Fintype V] in
lemma oriented_cross {c:V→Z→Bool} (f g:I→Z) (π:Equiv.Perm I) (v:V)
    (h:(∀ i,bit (c v (f i))≤bit (c v (g (π i)))) ∨
      (∀ i,bit (c v (g (π i)))≤bit (c v (f i)))):
    (∑ i,cross c f g π v i)=|(∑ i,bit (c v (f i)))-(∑ i,bit (c v (g i)))|:=by
  have he:(∑ i,bit (c v (g (π i))))=∑ i,bit (c v (g i)):=Equiv.sum_comp π (fun i=>bit (c v (g i)))
  rw [←he,←sum_sub_distrib]
  rcases h with h|h
  · rw [abs_of_nonpos (sum_nonpos (fun i _=>sub_nonpos.mpr (h i))),←sum_neg_distrib]
    apply sum_congr rfl
    intro i _
    exact abs_of_nonpos (sub_nonpos.mpr (h i))
  · rw [abs_of_nonneg (sum_nonneg (fun i _=>sub_nonneg.mpr (h i)))]
    exact sum_congr rfl (fun i _=>abs_of_nonneg (sub_nonneg.mpr (h i)))

/-- One matching is optimal at every member of the laminar family. -/
theorem exists_simultaneous {c:V→Z→Bool} (hc:Laminar c) (f g:I→Z):
    ∃ π:Equiv.Perm I,∀ v,(∑ i,cross c f g π v i)=
      |(∑ i,bit (c v (f i)))-(∑ i,bit (c v (g i)))|:=by
  obtain ⟨π,_,hm⟩:=Finset.exists_min_image (univ:Finset (Equiv.Perm I)) (cost c f g) univ_nonempty
  refine ⟨π,fun v=>oriented_cross f g π v ?_⟩
  exact minimizing_oriented hc f g π (fun ρ=>hm ρ (mem_univ _)) v

end KServer.LaminarMatching

end


/-! The concrete parent-ordered tree's descendant cuts form a laminar family. -/
noncomputable section
namespace KServer.Rounding
variable {n:ℕ} [NeZero n]

lemma Tree.under_trans (T:Tree n) (a b c:Fin n)
    (hab:T.under a b=true) (hbc:T.under b c=true):T.under a c=true:=by
  by_cases hcb:c=b
  · simpa only [hcb] using hab
  by_cases hc:c=0
  · subst c
    have hb:b=0:=by simpa only [Tree.under_zero,beq_iff_eq] using hbc
    exact False.elim (hcb hb.symm)
  have hp:T.under b (T.parent c)=true:=by
    rw [Tree.under,ite_eq_right hcb,dite_eq_right hc] at hbc
    exact hbc
  have ha:=T.under_trans a b (T.parent c) hab hp
  by_cases hca:c=a
  · rw [hca]; exact T.under_self a
  · rw [Tree.under,ite_eq_right hca,dite_eq_right hc]
    exact ha
termination_by c.val
decreasing_by exact T.lower c hc

lemma Tree.ancestors_comparable (T:Tree n) (a b c:Fin n)
    (ha:T.under a c=true) (hb:T.under b c=true):
    T.under a b=true ∨ T.under b a=true:=by
  by_cases hca:c=a
  · exact Or.inr (hca ▸ hb)
  by_cases hcb:c=b
  · exact Or.inl (hcb ▸ ha)
  by_cases hc:c=0
  · subst c
    have haa:a=0:=by simpa only [Tree.under_zero,beq_iff_eq] using ha
    exact False.elim (hca haa.symm)
  have ha':T.under a (T.parent c)=true:=by
    rw [Tree.under,ite_eq_right hca,dite_eq_right hc] at ha
    exact ha
  have hb':T.under b (T.parent c)=true:=by
    rw [Tree.under,ite_eq_right hcb,dite_eq_right hc] at hb
    exact hb
  exact T.ancestors_comparable a b (T.parent c) ha' hb'
termination_by c.val
decreasing_by exact T.lower c hc

lemma Tree.laminar (T:Tree n):LaminarMatching.Laminar T.under:=by
  intro v w
  by_cases hvw:T.under v w=true
  · right; left; intro z hz; exact T.under_trans v w z hvw hz
  by_cases hwv:T.under w v=true
  · left; intro z hz; exact T.under_trans w v z hwv hz
  right; right
  intro z hz
  cases hh:T.under w z
  · rfl
  · exact False.elim ((T.ancestors_comparable v w z hz hh).elim hvw hwv)

end KServer.Rounding

end


/-! Metric movement of the simultaneous laminar matching. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.Rounding
variable {n:ℕ} [NeZero n]
attribute [local instance] Classical.propDecidable Classical.decEq

def Tree.cutDistance (T:Tree n) (w:Fin n→ℝ) (u v:Fin n):ℝ:=
  ∑ z,w z*|T.indicator z u-T.indicator z v|

lemma Tree.cutDistance_symm (T:Tree n) (w:Fin n→ℝ) (u v:Fin n):
    T.cutDistance w u v=T.cutDistance w v u:=by
  unfold Tree.cutDistance
  exact sum_congr rfl (fun z _=>congrArg (w z*·) (abs_sub_comm _ _))

lemma Tree.cutDistance_self (T:Tree n) (w:Fin n→ℝ) (u:Fin n):T.cutDistance w u u=0:=by
  simp only [Tree.cutDistance,sub_self,abs_zero,mul_zero,sum_const_zero]

lemma Tree.cutDistance_peel (T:Tree n) (w:Fin n→ℝ) (u v:Fin n)
    (hu:u≠0) (hv:T.under u v=false):
    T.cutDistance w u v=T.cutDistance w (T.parent u) v+w u:=by
  have h:∀ z,w z*|T.indicator z u-T.indicator z v|=
      w z*|T.indicator z (T.parent u)-T.indicator z v|+(if z=u then w u else 0):=by
    intro z
    by_cases hz:z=u
    · subst z
      simp [Tree.indicator,T.under_self,T.under_parent_self u hu,hv]
    · have hh:=T.indicator_parent z u hu
      rw [ite_eq_right (Ne.symm hz)] at hh
      rw [sub_eq_zero.mp hh,ite_eq_right hz,add_zero]
  simp only [Tree.cutDistance,h,sum_add_distrib,sum_ite_eq',mem_univ,ite_true]

lemma Tree.under_false_of_lt (T:Tree n) (u v:Fin n) (hv:v.val<u.val):T.under u v=false:=by
  cases he:T.under u v
  · rfl
  · have :=T.under_le u v he
    omega

theorem Tree.metric_le_cutDistance {X:Type*} [PseudoMetricSpace X] (T:Tree n)
    (a:Fin n→X) (w:Fin n→ℝ)
    (he:∀ u,u≠0→dist (a u) (a (T.parent u))≤w u) (u v:Fin n):
    dist (a u) (a v)≤T.cutDistance w u v:=by
  by_cases huv:u=v
  · subst v; rw [dist_self,T.cutDistance_self]
  by_cases huv':v.val<u.val
  · have hu:u≠0:=by intro hu; simp [hu] at huv'
    rw [T.cutDistance_peel w u v hu (T.under_false_of_lt u v huv')]
    have hi:=T.metric_le_cutDistance a w he (T.parent u) v
    have ht:=dist_triangle (a u) (a (T.parent u)) (a v)
    linarith [he u hu]
  · have hlt:u.val<v.val:=by have hne:u.val≠v.val:=fun h=>huv (Fin.ext h); omega
    have hv:v≠0:=by intro hv; simp [hv] at hlt
    rw [T.cutDistance_symm w u v,T.cutDistance_peel w v u hv (T.under_false_of_lt v u hlt)]
    have hi:=T.metric_le_cutDistance a w he (T.parent v) u
    have ht:=dist_triangle (a v) (a (T.parent v)) (a u)
    rw [dist_comm (a v) (a u)] at ht
    linarith [he v hv]
termination_by u.val+v.val
decreasing_by all_goals have :=T.lower _ (by assumption); omega

/-- Actual permutation, not an assumed coupling cost bound. -/
theorem Tree.exists_metric_matching {X I:Type*} [PseudoMetricSpace X] [Fintype I]
    (T:Tree n) (a:Fin n→X) (w:Fin n→ℝ)
    (he:∀ u,u≠0→dist (a u) (a (T.parent u))≤w u) (f g:I→Fin n):
    ∃ π:Equiv.Perm I,(∑ i,dist (a (f i)) (a (g (π i))))≤
      ∑ v,w v*|(∑ i,T.indicator v (f i))-(∑ i,T.indicator v (g i))|:=by
  obtain ⟨π,hπ⟩:=LaminarMatching.exists_simultaneous T.laminar f g
  refine ⟨π,?_⟩
  calc
    (∑ i,dist (a (f i)) (a (g (π i))))≤∑ i,T.cutDistance w (f i) (g (π i)):=
      sum_le_sum (fun i _=>T.metric_le_cutDistance a w he _ _)
    _ = ∑ v,w v*|(∑ i,T.indicator v (f i))-(∑ i,T.indicator v (g i))|:=by
      unfold Tree.cutDistance
      rw [sum_comm]
      apply sum_congr rfl
      intro v _
      rw [←mul_sum]
      congr 1
      exact hπ v

end KServer.Rounding

end


/-! A deepest common ancestor exposes a discrepant cut. This permits bounds
using witnesses only at occupied endpoints; no empty-prefix anchor edge is
assumed short. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.Rounding
attribute [local instance] Classical.propDecidable Classical.decEq
variable {n:ℕ} [NeZero n]

lemma Tree.parent_under (T:Tree n) (u:Fin n):T.under (T.parent u) u=true:=by
  by_cases hu:u=0
  · subst u; rw [T.root]; exact T.under_self 0
  have hn:u≠T.parent u:=by intro he; have hh:=T.lower u hu; have hv:=congrArg Fin.val he; omega
  rw [Tree.under,ite_eq_right hn,dite_eq_right hu]
  exact T.under_self _

lemma Tree.path_child (T:Tree n) (p u:Fin n) (h:T.under p u=true) (hne:p≠u):
    ∃ z:Fin n,z≠0 ∧ T.parent z=p ∧ T.under z u=true:=by
  have hu:u≠0:=by
    intro hu
    subst u
    have hp:p=0:=by simpa only [Tree.under_zero,beq_iff_eq] using h
    exact hne hp
  by_cases he:T.parent u=p
  · exact ⟨u,hu,he,T.under_self u⟩
  have hh:T.under p (T.parent u)=true:=by
    rw [Tree.under,ite_eq_right (Ne.symm hne),dite_eq_right hu] at h
    exact h
  obtain ⟨z,hz,hp,hs⟩:=T.path_child p (T.parent u) hh (Ne.symm he)
  exact ⟨z,hz,hp,T.under_trans z (T.parent u) u hs (T.parent_under u)⟩
termination_by u.val
decreasing_by exact T.lower u hu

lemma Tree.common_cut (T:Tree n) (u v:Fin n) (hne:u≠v):
    ∃ p z:Fin n,T.under p u=true ∧ T.under p v=true ∧ T.parent z=p ∧
      T.under z u≠T.under z v:=by
  let F:Finset (Fin n):=univ.filter (fun p=>T.under p u=true ∧ T.under p v=true)
  have hF:F.Nonempty:=⟨0,mem_filter.mpr ⟨mem_univ _,T.under_root u,T.under_root v⟩⟩
  let p:=F.max' hF
  have hp:p∈F:=max'_mem F hF
  have hp1:T.under p u=true:=(mem_filter.mp hp).2.1
  have hp2:T.under p v=true:=(mem_filter.mp hp).2.2
  have hzfalse:∀ z,z≠0→T.parent z=p→T.under z u=true→T.under z v=true→False:=by
    intro z hz he hzu hzv
    have hzF:z∈F:=mem_filter.mpr ⟨mem_univ _,hzu,hzv⟩
    have hl:z≤p:=le_max' F z hzF
    have hh:=T.lower z hz
    rw [he] at hh
    exact (not_lt_of_ge hl hh)
  by_cases hpu:p=u
  · obtain ⟨z,hz,he,hzv⟩:=T.path_child p v hp2 (by simpa only [hpu] using hne)
    exact ⟨p,z,hp1,hp2,he,fun hze=>hzfalse z hz he (hze.trans hzv) hzv⟩
  · obtain ⟨z,hz,he,hzu⟩:=T.path_child p u hp1 hpu
    exact ⟨p,z,hp1,hp2,he,fun hze=>hzfalse z hz he hzu (hze.symm.trans hzu)⟩

lemma Tree.distinct_le_cut {X:Type*} [PseudoMetricSpace X] (T:Tree n)
    (w:Fin n→ℝ) (hw:∀ z,0≤w z) {C:ℝ} (hC:0≤C)
    (a b:X) (u v:Fin n) (hne:u≠v)
    (hc:∀ p,T.under p u=true→T.under p v=true→dist a b≤C*w p):
    dist a b≤C*T.cutDistance (fun z=>w (T.parent z)) u v:=by
  obtain ⟨p,z,hp1,hp2,he,hz⟩:=T.common_cut u v hne
  have hbit:|T.indicator z u-T.indicator z v|=1:=by
    unfold Tree.indicator
    cases h1:T.under z u <;> cases h2:T.under z v <;> simp_all
  have hh:w p≤T.cutDistance (fun z=>w (T.parent z)) u v:=by
    have hs:=single_le_sum (s:=(univ:Finset (Fin n))) (f:=fun z=>w (T.parent z)*|T.indicator z u-T.indicator z v|)
      (fun z _=>mul_nonneg (hw _) (abs_nonneg _)) (mem_univ z)
    simpa only [he,hbit,mul_one,Tree.cutDistance] using hs
  exact (hc p hp1 hp2).trans (mul_le_mul_of_nonneg_left hh hC)
end KServer.Rounding

end


/-! Every ancestor of an occupied word is witnessed by the same point. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.PrefixTree
attribute [local instance] Classical.propDecidable Classical.decEq
variable (A:Type) [Fintype A] (L:ℕ)

omit [Fintype A] in
lemma hit_parent {Y:Type} (maps:ℕ→Y→A) (v:Vertex A L) (y:Y)
    (hy:HierarchyCounts.hit maps v.2 y):
    HierarchyCounts.hit maps (parent A L v).2 y:=by
  rcases v with ⟨⟨d,hd⟩,f⟩
  cases d with
  | zero=>intro i; exact Fin.elim0 i
  | succ d=>
    rw [parent_succ]
    intro i
    exact hy i.castSucc

lemma under_depth (u v:Node A L) (h:(travelTree A L).under u v=true):
    depth A L u≤depth A L v:=by
  by_cases he:v=u
  · subst v; exact le_rfl
  have hv:v≠0:=by
    intro h0; subst v
    have hu:u=0:=by simpa only [Rounding.Tree.under_zero,beq_iff_eq] using h
    exact he hu.symm
  rw [Rounding.Tree.under,ite_eq_right he,dite_eq_right hv] at h
  have ih:=under_depth u ((travelTree A L).parent v) h
  have hd:0<(numbering A L v).1.val:=by
    apply Nat.pos_of_ne_zero
    intro hh
    exact hv ((numbering_eq_root A L v).mp ((depth_zero_iff A L _).mp hh))
  change (numbering A L u).1.val≤(numbering A L v).1.val
  change (numbering A L u).1.val≤(numbering A L ((travelTree A L).parent v)).1.val at ih
  rw [numbering_parent,parent_depth A L _ hd] at ih
  omega
termination_by v.val
decreasing_by exact (travelTree A L).lower v hv

lemma under_hit {Y:Type} (maps:ℕ→Y→A) (u v:Node A L)
    (h:(travelTree A L).under u v=true) (y:Y)
    (hy:HierarchyCounts.hit maps (numbering A L v).2 y):
    HierarchyCounts.hit maps (numbering A L u).2 y:=by
  by_cases he:v=u
  · subst v; exact hy
  have hv:v≠0:=by
    intro h0; subst v
    have hu:u=0:=by simpa only [Rounding.Tree.under_zero,beq_iff_eq] using h
    exact he hu.symm
  rw [Rounding.Tree.under,ite_eq_right he,dite_eq_right hv] at h
  apply under_hit maps u ((travelTree A L).parent v) h y
  rw [numbering_parent]
  exact hit_parent A L maps _ y hy
termination_by v.val
decreasing_by exact (travelTree A L).lower v hv

end KServer.PrefixTree

end


/-! Geometric comparisons only at witnessed occupied words. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.PrefixTree
attribute [local instance] Classical.propDecidable Classical.decEq
variable (A:Type) [Fintype A] (L:ℕ)
variable {Y:Type} [MetricSpace Y]

def nodeAnchor (z:Y) (a:ℕ→A→Y) (v:Node A L):Y:=
  match lastKey A L v with
  | none=>z
  | some key=>a (depth A L v-1) key

def nodeMotion (m:ℕ→A→ℝ) (v:Node A L):ℝ:=
  match lastKey A L v with
  | none=>0
  | some key=>m (depth A L v-1) key

lemma last_none (v:Node A L):lastKey A L v=none ↔ v=0:=by
  unfold lastKey
  split_ifs with h
  · simp only [false_iff]
    intro hv; subst v
    rw [depth,numbering_zero] at h
    change 0<0 at h
    omega
  · have hz:(numbering A L v).1.val=0:=by change ¬0<(numbering A L v).1.val at h; omega
    have hv:= (numbering_eq_root A L v).mp ((depth_zero_iff A L _).mp hz)
    simp only [hv]

lemma last_depth {v:Node A L} {key:A} (h:lastKey A L v=some key):
    0<depth A L v ∧ v∈band A L (depth A L v-1) key:=by
  have hd:0<depth A L v:=by
    by_contra hh
    simp only [lastKey,dite_eq_right hh] at h
    cases h
  exact ⟨hd,mem_filter.mpr ⟨mem_univ _,by omega,h⟩⟩

lemma weight_under {R τ:ℝ} (hR:0≤R) (hτ:1≤τ) {u v:Node A L}
    (h:(travelTree A L).under u v=true):
    weight A L R τ v≤weight A L R τ u:=
  ParkedCoefficients.radius_antitone hR hτ (under_depth A L u v h)

lemma anchor_witness (z:Y) (a:ℕ→A→Y) (maps:ℕ→Y→A) {R τ:ℝ}
    (ha:∀ d,d<L→∀ y,dist (a d (maps d y)) y≤20*(R/τ^(d+1)))
    (v:Node A L) (hv:v≠0) (y:Y) (hy:HierarchyCounts.hit maps (numbering A L v).2 y):
    dist (nodeAnchor A L z a v) y≤20*weight A L R τ v:=by
  cases he:lastKey A L v with
  | none=>exact False.elim (hv ((last_none A L v).mp he))
  | some key=>
    obtain ⟨hd,hb⟩:=last_depth A L he
    have hkey:=band_key A L maps (depth A L v-1) key hb y hy
    have hL:depth A L v-1<L:=by have hh:=(numbering A L v).1.isLt; change depth A L v<L+1 at hh; omega
    have hh:=ha (depth A L v-1) hL y
    rw [hkey] at hh
    have hdep:depth A L v-1+1=depth A L v:=by omega
    rw [hdep] at hh
    simpa only [nodeAnchor,he,weight,depth] using hh

lemma witnessed_common_bound (z:Y) (a b:ℕ→A→Y) (maps next:ℕ→Y→A) {R τ:ℝ}
    (hR:0≤R) (hτ:1≤τ) (hdia:∀ x y:Y,dist x y≤R)
    (ha:∀ d,d<L→∀ y,dist (a d (maps d y)) y≤20*(R/τ^(d+1)))
    (hb:∀ d,d<L→∀ y,dist (b d (next d y)) y≤20*(R/τ^(d+1)))
    (hab:∀ d,d<L→∀ x y key,maps d x=key→next d y=key→dist (a d key) (b d key)≤40*(R/τ^(d+1)))
    (u v p:Node A L) (hpu:(travelTree A L).under p u=true) (hpv:(travelTree A L).under p v=true)
    (x y:Y) (hx:HierarchyCounts.hit maps (numbering A L u).2 x)
    (hy:HierarchyCounts.hit next (numbering A L v).2 y):
    dist (nodeAnchor A L z a u) (nodeAnchor A L z b v)≤120*weight A L R τ p:=by
  by_cases hp:p=0
  · subst p
    have hw:weight A L R τ (0:Node A L)=R:=by
      rw [weight,numbering_zero]
      change R/τ^0=R
      simp
    rw [hw]
    exact (hdia _ _).trans (by nlinarith)
  have hdu:0<depth A L p:=by
    apply Nat.pos_of_ne_zero
    intro hh
    exact hp ((numbering_eq_root A L p).mp ((depth_zero_iff A L _).mp hh))
  have hz:depth A L (0:Node A L)=0:=by rw [depth,numbering_zero]; rfl
  have hu:u≠0:=by intro he; subst u; have hh:=under_depth A L p 0 hpu; rw [hz] at hh; omega
  have hv:v≠0:=by intro he; subst v; have hh:=under_depth A L p 0 hpv; rw [hz] at hh; omega
  have hxp:=under_hit A L maps p u hpu x hx
  have hyp:=under_hit A L next p v hpv y hy
  have h1:=anchor_witness A L z a maps ha u hu x hx
  have h2:=anchor_witness A L z a maps ha p hp x hxp
  have h3:=anchor_witness A L z b next hb p hp y hyp
  have h4:=anchor_witness A L z b next hb v hv y hy
  have huW:=weight_under A L hR hτ hpu
  have hvW:=weight_under A L hR hτ hpv
  have hm:dist (nodeAnchor A L z a p) (nodeAnchor A L z b p)≤40*weight A L R τ p:=by
    cases he:lastKey A L p with
    | none=>exact False.elim (hp ((last_none A L p).mp he))
    | some key=>
      obtain ⟨hp0,hpb⟩:=last_depth A L he
      have hL:depth A L p-1<L:=by have hh:=(numbering A L p).1.isLt; change depth A L p<L+1 at hh; omega
      have hh:=hab (depth A L p-1) hL x y key
        (band_key A L maps _ key hpb x hxp) (band_key A L next _ key hpb y hyp)
      have hd:depth A L p-1+1=depth A L p:=by omega
      rw [hd] at hh
      simpa only [nodeAnchor,he,weight,depth] using hh
  have ht1:=dist_triangle (nodeAnchor A L z a u) x (nodeAnchor A L z a p)
  have ht2:=dist_triangle (nodeAnchor A L z b p) y (nodeAnchor A L z b v)
  rw [dist_comm x (nodeAnchor A L z a p)] at ht1
  rw [dist_comm y (nodeAnchor A L z b v)] at ht2
  have ht3:=dist_triangle4 (nodeAnchor A L z a u) (nodeAnchor A L z a p)
    (nodeAnchor A L z b p) (nodeAnchor A L z b v)
  linarith
end KServer.PrefixTree

end


/-! An actual labeled list of k occupied vertices for every consistent
nonnegative integral count state. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.TreeRounding
open Rounding
attribute [local instance] Classical.propDecidable Classical.decEq
variable {n k:ℕ} [NeZero n]

def Tree.toTravel (T:Tree n):Rounding.Tree n where
  parent:=T.parent
  root:=T.root
  lower:=T.lower

lemma Tree.consistent_park (T:Tree n) (c:Counts n) (hc:T.Consistent c) (v:Fin n):
    (c.park v:ℝ)=T.park (fun u=>(c.subtree u:ℝ)) v:=by
  have hh:((c.park v:ℝ)+(∑ u:T.Child v,(c.subtree u.val:ℝ)))=(c.subtree v:ℝ):=by
    exact_mod_cast hc v
  unfold Tree.park
  linarith

lemma Tree.park_nats_sum (T:Tree n) (c:Counts n) (hc:T.Consistent c)
    (hp:∀ v,0≤c.park v) (hr:c.subtree 0=(k:ℤ)):
    (∑ v,(c.park v).toNat)=k:=by
  apply Nat.cast_injective (R:=ℝ)
  rw [Nat.cast_sum]
  have hh:=T.toTravel.park_subtree_total (fun u=>(c.subtree u:ℝ)) 0
  have hi:∀ v,T.toTravel.indicator 0 v=1:=by
    intro v
    simp only [Rounding.Tree.indicator,Rounding.Tree.under_root,ite_true]
  simp only [hi,one_mul] at hh
  calc
    (∑ v,((c.park v).toNat:ℝ))=∑ v,(c.park v:ℝ):=by
      apply sum_congr rfl; intro v _
      exact_mod_cast Int.toNat_of_nonneg (hp v)
    _ = ∑ v,T.toTravel.park (fun u=>(c.subtree u:ℝ)) v:=by
      apply sum_congr rfl; intro v _; exact T.consistent_park c hc v
    _ = (k:ℝ):=by rw [hh,hr]; rfl

def countEquiv (T:Tree n) (c:Counts n) (hc:T.Consistent c)
    (hp:∀ v,0≤c.park v) (hr:c.subtree 0=(k:ℤ)):
    (Σ v:Fin n,Fin (c.park v).toNat)≃Fin k:=
  Fintype.equivOfCardEq (by simpa only [Fintype.card_sigma,Fintype.card_fin] using T.park_nats_sum c hc hp hr)

def slots (T:Tree n) (c:Counts n) (hc:T.Consistent c)
    (hp:∀ v,0≤c.park v) (hr:c.subtree 0=(k:ℤ)) (i:Fin k):Fin n:=
  ((countEquiv T c hc hp hr).symm i).1

lemma slots_sum (T:Tree n) (c:Counts n) (hc:T.Consistent c)
    (hp:∀ v,0≤c.park v) (hr:c.subtree 0=(k:ℤ)) (f:Fin n→ℝ):
    (∑ i:Fin k,f (slots T c hc hp hr i))=∑ v,(c.park v:ℝ)*f v:=by
  unfold slots
  rw [Equiv.sum_comp (countEquiv T c hc hp hr).symm (fun p=>f p.1)]
  simp only [Fintype.sum_sigma,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]
  apply sum_congr rfl
  intro v _
  have he : ((c.park v).toNat:ℝ)=(c.park v:ℝ):=by
    exact_mod_cast Int.toNat_of_nonneg (hp v)
  rw [he]

lemma slots_subtree (T:Tree n) (c:Counts n) (hc:T.Consistent c)
    (hp:∀ v,0≤c.park v) (hr:c.subtree 0=(k:ℤ)) (u:Fin n):
    (∑ i:Fin k,T.toTravel.indicator u (slots T c hc hp hr i))=(c.subtree u:ℝ):=by
  rw [slots_sum]
  simp_rw [T.consistent_park c hc,mul_comm (T.park _ _) (T.toTravel.indicator _ _)]
  exact T.toTravel.park_subtree_total _ u

lemma slots_positive (T:Tree n) (c:Counts n) (hc:T.Consistent c)
    (hp:∀ v,0≤c.park v) (hr:c.subtree 0=(k:ℤ)) (i:Fin k):0<c.park (slots T c hc hp hr i):=by
  have hi:=((countEquiv T c hc hp hr).symm i).2.isLt
  change _<(c.park (slots T c hc hp hr i)).toNat at hi
  omega

end KServer.TreeRounding

end


/-! Cross-time occupied-endpoint matching, without any edge hypothesis on
empty words. New endpoint anchor drift is paid only for coincident vertices. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.Rounding
attribute [local instance] Classical.propDecidable Classical.decEq
variable {n:ℕ} [NeZero n]

theorem Tree.exists_cross_matching {X I:Type*} [PseudoMetricSpace X] [Fintype I]
    (T:Tree n) (a b:Fin n→X) (w D:Fin n→ℝ) (hD:∀ v,0≤D v)
    {C:ℝ} (f g:I→Fin n)
    (hneq:∀ i j,f i≠g j→dist (a (f i)) (b (g j))≤C*T.cutDistance w (f i) (g j))
    (heq:∀ i j,f i=g j→dist (a (f i)) (b (g j))≤D (g j)):
    ∃ π:Equiv.Perm I,(∑ i,dist (a (f i)) (b (g (π i))))≤
      C*(∑ v,w v*|(∑ i,T.indicator v (f i))-(∑ i,T.indicator v (g i))|)+∑ i,D (g i):=by
  obtain ⟨π,hπ⟩:=LaminarMatching.exists_simultaneous T.laminar f g
  refine ⟨π,?_⟩
  have hh:∀ i,dist (a (f i)) (b (g (π i)))≤C*T.cutDistance w (f i) (g (π i))+D (g (π i)):=by
    intro i
    by_cases he:f i=g (π i)
    · rw [he,T.cutDistance_self,mul_zero,zero_add]
      simpa only [he] using heq i (π i) he
    · exact (hneq i (π i) he).trans (le_add_of_nonneg_right (hD _))
  calc
    _ ≤∑ i,(C*T.cutDistance w (f i) (g (π i))+D (g (π i))):=sum_le_sum (fun i _=>hh i)
    _ = C*(∑ v,w v*|(∑ i,T.indicator v (f i))-(∑ i,T.indicator v (g i))|)+∑ i,D (g i):=by
      rw [sum_add_distrib,←mul_sum,Equiv.sum_comp π (fun i=>D (g i))]
      congr 1
      congr 1
      unfold Tree.cutDistance
      rw [sum_comm]
      apply sum_congr rfl
      intro v _
      rw [←mul_sum]
      congr 1
      exact hπ v
end KServer.Rounding

end


/-! The fixed finite inventory of integral count states with total mass k.
The encoding is an actual k-slot list, not a bound on future randomness. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.TreeRounding
attribute [local instance] Classical.propDecidable Classical.decEq
variable {n k:ℕ} [NeZero n]

def Good (T:Tree n) (k:ℕ) (c:Counts n):Prop:=
  T.Consistent c ∧ (∀ v,0≤ c.park v) ∧ c.subtree 0=(k:ℤ)
abbrev Inventory (T:Tree n) (k:ℕ):= {c:Counts n //Good T k c}

def Inventory.slots (T:Tree n) (c:Inventory T k):Fin k→Fin n:=
  TreeRounding.slots T c.val c.property.1 c.property.2.1 c.property.2.2

lemma Inventory.slots_injective (T:Tree n):Function.Injective (Inventory.slots (k:=k) T):=by
  intro c d he
  have hsub: c.val.subtree=d.val.subtree:=by
    funext u
    apply Int.cast_injective (α:=ℝ)
    have h1:=slots_subtree T c.val c.property.1 c.property.2.1 c.property.2.2 u
    have h2:=slots_subtree T d.val d.property.1 d.property.2.1 d.property.2.2 u
    change (∑ i,T.toTravel.indicator u (Inventory.slots T c i))=_ at h1
    change (∑ i,T.toTravel.indicator u (Inventory.slots T d i))=_ at h2
    rw [he] at h1
    exact h1.symm.trans h2
  have hpark:c.val.park=d.val.park:=by
    funext u
    apply Int.cast_injective (α:=ℝ)
    rw [T.consistent_park c.val c.property.1,T.consistent_park d.val d.property.1,hsub]
  apply Subtype.ext
  have hh : ∀ (c d : Counts n), c.subtree=d.subtree → c.park=d.park → c=d := by
    intro c d h1 h2
    cases c; cases d
    simp only [Counts.mk.injEq] at *
    exact ⟨h1,h2⟩
  exact hh _ _ hsub hpark

instance inventoryFintype (T:Tree n):Fintype (Inventory T k):=
  Fintype.ofInjective (Inventory.slots T) (Inventory.slots_injective T)

lemma stock_good (T:Tree n):Good T k (stock (k:ℤ)):=by
  have hh:=stock_valid T (Int.natCast_nonneg k)
  exact ⟨hh.2.2,fun v=>(hh.2.1 v).1,by simp only [stock,ite_true]⟩

instance inventoryNonempty (T:Tree n):Nonempty (Inventory T k):=⟨⟨stock (k:ℤ),stock_good T⟩⟩

def pack (T:Tree n) (c:Counts n):Inventory T k:=
  if h:Good T k c then ⟨c,h⟩ else ⟨stock (k:ℤ),stock_good T⟩
lemma pack_val (T:Tree n) (c:Counts n) (hc:Good T k c):(pack T c:Inventory T k).val=c:=by
  simp only [pack,dite_eq_left hc]

lemma good_of_valid (T:Tree n) (a:Fin n→ℝ) (ha0:a 0=(k:ℝ)) (c:Counts n) (hc:T.Valid a c):Good T k c:=by
  refine ⟨hc.2.2,fun v=>(hc.2.1 v).1,?_⟩
  exact balanced_integer (by exact_mod_cast ha0) ((hc.1 0).2)

end KServer.TreeRounding

end


/-! Genuine occupied-slot matching on the complete prefix tree. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.PrefixTree
attribute [local instance] Classical.propDecidable Classical.decEq
variable (A:Type) [Fintype A] (L:ℕ)
variable {Y:Type} [MetricSpace Y] {k:ℕ}

def countConfig (z:Y) (a:ℕ→A→Y) (c:TreeRounding.Inventory (tree A L) k):Configuration k Y:=
  fun i=>nodeAnchor A L z a (c.slots (tree A L) i)

lemma count_matching (z:Y) (a b:ℕ→A→Y) (maps next:ℕ→Y→A) (m:ℕ→A→ℝ) {R τ:ℝ}
    (hR:0≤R) (hτ:1≤τ) (hdia:∀ x y:Y,dist x y≤R)
    (ha:∀ d,d<L→∀ y,dist (a d (maps d y)) y≤20*(R/τ^(d+1)))
    (hb:∀ d,d<L→∀ y,dist (b d (next d y)) y≤20*(R/τ^(d+1)))
    (hab:∀ d,d<L→∀ x y key,maps d x=key→next d y=key→dist (a d key) (b d key)≤40*(R/τ^(d+1)))
    (hm:∀ d key,0 ≤ m d key)
    (hmab:∀ d,d<L→∀ x y key,maps d x=key→next d y=key→dist (a d key) (b d key)≤40*m d key)
    (c e:TreeRounding.Inventory (tree A L) k)
    (hc:∀ i,∃ x,HierarchyCounts.hit maps (numbering A L (c.slots (tree A L) i)).2 x)
    (he:∀ i,∃ y,HierarchyCounts.hit next (numbering A L (e.slots (tree A L) i)).2 y):
    matching (countConfig A L z a c) (countConfig A L z b e)≤
      120*(∑ v,weight A L R τ ((tree A L).parent v)*|(c.val.subtree v:ℝ)-(e.val.subtree v:ℝ)|)+
        40*(∑ v,(e.val.park v:ℝ)*nodeMotion A L m v):=by
  let D:=fun v:Node A L=>40*nodeMotion A L m v
  have hD:∀ v,0≤D v:=by
    intro v
    dsimp only [D,nodeMotion]
    cases lastKey A L v with
    | none=>norm_num
    | some key=>exact mul_nonneg (by norm_num) (hm _ _)
  have hneq:∀ i j,c.slots (tree A L) i≠e.slots (tree A L) j→
      dist (nodeAnchor A L z a (c.slots (tree A L) i)) (nodeAnchor A L z b (e.slots (tree A L) j))≤
        120*(travelTree A L).cutDistance (fun v=>weight A L R τ ((tree A L).parent v))
          (c.slots (tree A L) i) (e.slots (tree A L) j):=by
    intro i j hne
    obtain ⟨x,hx⟩:=hc i
    obtain ⟨y,hy⟩:=he j
    exact (travelTree A L).distinct_le_cut (weight A L R τ) (weight_nonneg A L hR (by linarith))
      (by norm_num) _ _ _ _ hne (fun p hu hv=>witnessed_common_bound A L z a b maps next
        hR hτ hdia ha hb hab _ _ p hu hv x y hx hy)
  have heq:∀ i j,c.slots (tree A L) i=e.slots (tree A L) j→
      dist (nodeAnchor A L z a (c.slots (tree A L) i)) (nodeAnchor A L z b (e.slots (tree A L) j))≤D (e.slots (tree A L) j):=by
    intro i j hij
    obtain ⟨x,hx⟩:=hc i
    obtain ⟨y,hy⟩:=he j
    rw [hij] at hx ⊢
    let v:=e.slots (tree A L) j
    change dist (nodeAnchor A L z a v) (nodeAnchor A L z b v)≤D v
    cases hl:lastKey A L v with
    | none=>simp only [D,nodeAnchor,nodeMotion,hl,dist_self,mul_zero,le_refl]
    | some key=>
      obtain ⟨hp,hmem⟩:=last_depth A L hl
      have hL:depth A L v-1<L:=by have hh:=(numbering A L v).1.isLt; change depth A L v<L+1 at hh; omega
      simp only [nodeAnchor,nodeMotion,hl,D]
      exact hmab _ hL x y key (band_key A L maps _ key hmem x hx) (band_key A L next _ key hmem y hy)
  obtain ⟨π,hπ⟩:=(travelTree A L).exists_cross_matching (nodeAnchor A L z a) (nodeAnchor A L z b)
    (fun v=>weight A L R τ ((tree A L).parent v)) D hD (c.slots _) (e.slots _) hneq heq
  apply (matching_le _ _ π).trans
  change (∑ i,dist (nodeAnchor A L z a (c.slots _ i)) (nodeAnchor A L z b (e.slots _ (π i))))≤_
  have hsub (c:TreeRounding.Inventory (tree A L) k) (v:Node A L):
      (∑ i,(travelTree A L).indicator v (c.slots _ i))=(c.val.subtree v:ℝ):=
    TreeRounding.slots_subtree _ c.val c.property.1 c.property.2.1 c.property.2.2 v
  simp only [hsub] at hπ
  have hs:(∑ i,D (e.slots _ i))=40*(∑ v,(e.val.park v:ℝ)*nodeMotion A L m v):=by
    change (∑ i,D (TreeRounding.slots (tree A L) e.val e.property.1 e.property.2.1 e.property.2.2 i))=_
    rw [TreeRounding.slots_sum]
    dsimp only [D]
    rw [mul_sum]
    apply sum_congr rfl
    intro v _
    ring
  rwa [hs] at hπ
end KServer.PrefixTree

end


/-! Rounded occupied vertices have positive fractional park, and all positive
integer parks occur in the actual labeled list. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.TreeRounding
attribute [local instance] Classical.propDecidable Classical.decEq
variable {n k:ℕ} [NeZero n]

lemma Inventory.slot_exists (T:Tree n) (c:Inventory T k) (v:Fin n) (hv:0<c.val.park v):
    ∃ i,c.slots T i=v:=by
  let p:(Σ u:Fin n,Fin (c.val.park u).toNat):=⟨v,⟨0,by omega⟩⟩
  refine ⟨countEquiv T c.val c.property.1 c.property.2.1 c.property.2.2 p,?_⟩
  unfold Inventory.slots TreeRounding.slots
  rw [Equiv.symm_apply_apply]

lemma Inventory.valid_slot_positive (T:Tree n) (c:Inventory T k) (a:Fin n→ℝ)
    (ha:∀ v,0≤T.park a v) (hc:T.Valid a c.val) (i:Fin k):
    0<T.park a (c.slots T i):=by
  have hp:=slots_positive T c.val c.property.1 c.property.2.1 c.property.2.2 i
  change 0<c.val.park (c.slots T i) at hp
  apply lt_of_le_of_ne (ha _)
  intro he
  have hh:=balanced_integer (k:=0) (by simpa only [Int.cast_zero] using he.symm) ((hc.2.1 (c.slots T i)).2)
  have hh':c.val.park (c.slots T i)=0:=by exact hh
  omega

lemma balanced_one_le {a:ℝ} {j:ℤ} (ha:1≤a) (hj:Rounding.Balanced a j):1≤j:=by
  have hf:1≤Int.floor a:=by exact Int.le_floor.mpr (by simpa only [Int.cast_one] using ha)
  exact hf.trans ((Rounding.balanced_iff_bounds a j).mp hj).1
end KServer.TreeRounding

namespace KServer.PrefixTree
attribute [local instance] Classical.propDecidable Classical.decEq
variable (A:Type) [Fintype A] (L:ℕ)
variable {Y:Type} {k:ℕ}

lemma count_witness (c:TreeRounding.Inventory (tree A L) k) (q:Node A L→ℝ)
    (hp:∀ v,0≤(travelTree A L).park q v) (hq:∀ v,(travelTree A L).park q v≤q v)
    (hc:(tree A L).Valid q c.val) (maps:ℕ→Y→A)
    (hw:∀ v,0<q v→∃ x,HierarchyCounts.hit maps (numbering A L v).2 x) (i:Fin k):
    ∃ x,HierarchyCounts.hit maps (numbering A L (c.slots (tree A L) i)).2 x:=by
  have hh:=c.valid_slot_positive (tree A L) q hp hc i
  apply hw
  exact hh.trans_le (hq _)
end KServer.PrefixTree

end


/-! Exact fixed-band aggregation of the occupied anchor drift. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.PrefixTree
attribute [local instance] Classical.propDecidable Classical.decEq
variable (A:Type) [Fintype A] (L:ℕ)

lemma nodeMotion_sum (p:Node A L→ℝ) (m:ℕ→A→ℝ):
    (∑ v,p v*nodeMotion A L m v)=∑ d:Fin L,∑ a:A,m d.val a*bandMass A L p d.val a:=by
  simp only [bandMass,mul_sum,band,sum_filter]
  rw [sum_comm]
  conv_rhs => arg 2; ext a; rw [sum_comm]
  rw [sum_comm]
  apply sum_congr rfl
  intro v _
  cases hv:lastKey A L v with
  | none=>
    simp [nodeMotion,hv]
  | some a=>
    obtain ⟨hp,hb⟩:=last_depth A L hv
    have hd:depth A L v-1<L:=by have hh:=(numbering A L v).1.isLt; change depth A L v<L+1 at hh; omega
    have he:depth A L v=depth A L v-1+1:=by omega
    simp only [nodeMotion,hv,Option.some.injEq]
    rw [sum_eq_single a]
    · rw [sum_eq_single (⟨depth A L v-1,hd⟩:Fin L)]
      · rw [ite_eq_left ⟨he,rfl⟩]
        ring
      · intro d _ hne
        have hn:depth A L v≠d.val+1:=by intro hh; apply hne; apply Fin.ext; change d.val=depth A L v-1; omega
        simp only [hn,false_and,ite_false,mul_zero]
      · simp only [mem_univ,not_true_eq_false,false_implies]
    · intro b _ hne
      have hn:a≠b:=Ne.symm hne
      simp only [hn,and_false,ite_false,mul_zero,sum_const_zero]
    · simp only [mem_univ,not_true_eq_false,false_implies]
end KServer.PrefixTree

end

end OAI
