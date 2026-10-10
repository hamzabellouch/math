import Mathlib
import OAI.Combinatorics.KServer.JointTravel
import OAI.Combinatorics.KServer.MetricMatching

namespace OAI

/-! Common complete keys have controlled anchors. Only common moving heavy
labels incur chronological travel; tiers and singleton fallback are fixed. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.LevelKeys
open FiniteExperiment TierProcess HeavyAnchorDynamics
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Y:Type} [MetricSpace Y] [Fintype Y] {k H:ℕ} [NeZero k]
variable (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
variable {r:ℝ} (hr:0<r) (σ:Fin H→Y) (tape:Tape Y k H r)

lemma inl_key (t:ℕ) (x:Y) (a:Sigma (Alphabet Y k))
    (ha:map s law hr.le σ tape t x=Sum.inl a):
    keys s law hr.le σ tape t a.1 x=some a.2:=by
  unfold map PriorityKeys.key at ha
  cases hs:PriorityKeys.selected (keys s law hr.le σ tape t) x with
  | none=>rw [hs] at ha; cases ha
  | some z=>
    rw [hs] at ha
    have he:z=a:=Sum.inl.inj ha
    subst z
    exact (PriorityKeys.selected_some _ x hs).1

def motion (t:ℕ):Key Y k→ℝ
  | Sum.inl ⟨none,a⟩ => if HeavyAnchorDynamics.present s law r σ tape.1 t a ∧
      HeavyAnchorDynamics.present s law r σ tape.1 (t+1) a ∧
      heavyAnchor s law r σ tape.1 t a≠heavyAnchor s law r σ tape.1 (t+1) a then r else 0
  | _=>0

include hr in
lemma motion_nonneg (t:ℕ) (a:Key Y k):0 ≤ motion s law σ tape t a:=by
  cases a with
  | inr a=>rfl
  | inl z=>
    rcases z with ⟨i,a⟩
    cases i with
    | none=>change 0 ≤ if _ then r else 0; split_ifs <;> positivity
    | some i=>rfl

include hr in
lemma motion_le (t:ℕ) (a:Key Y k):motion s law σ tape t a≤r:=by
  cases a with
  | inr a=>exact hr.le
  | inl z=>
    rcases z with ⟨i,a⟩
    cases i with
    | none=>change (if _ then r else 0)≤r; split_ifs <;> linarith
    | some i=>exact hr.le

lemma common_anchor_motion (t:Fin H) (x y:Y) (a:Key Y k)
    (hx:map s law hr.le σ tape t.val x=a) (hy:map s law hr.le σ tape (t.val+1) y=a):
    dist (anchor s law hr.le σ tape t.val a) (anchor s law hr.le σ tape (t.val+1) a)≤
      40*motion s law σ tape t.val a:=by
  cases a with
  | inr a=>simp only [anchor,PriorityKeys.anchor,motion,dist_self,mul_zero,le_refl]
  | inl z=>
    rcases z with ⟨i,a⟩
    have hx':=inl_key s law hr σ tape t.val x ⟨i,a⟩ hx
    have hy':=inl_key s law hr σ tape (t.val+1) y ⟨i,a⟩ hy
    cases i with
    | some i=>
      let :Nonempty Y:=⟨s 0⟩
      have he:=TierKeys.anchors_persist (request s σ) hr.le (tierQualifies s law r σ i)
        (tape.2 i).1 (tape.2 i).2 t.val x y hx' hy'
      change dist (TierKeys.anchor _ _ _ _ _ _) (TierKeys.anchor _ _ _ _ _ _)≤40*0
      rw [he,dist_self,mul_zero]
    | none=>
      obtain ⟨c,hc,hlc,hdc⟩:=(HeavyAnchorDynamics.key_iff s law hr σ tape.1 t.val x a).mp hx'
      obtain ⟨d,hd,hld,hdd⟩:=(HeavyAnchorDynamics.key_iff s law hr σ tape.1 (t.val+1) y a).mp hy'
      have hec:=HeavyAnchorDynamics.anchor_eq s law hr σ tape.1 t.val hc hlc
      have hed:=HeavyAnchorDynamics.anchor_eq s law hr σ tape.1 (t.val+1) hd hld
      have hp:HeavyAnchorDynamics.present s law r σ tape.1 t.val a:=⟨c,hc,hlc⟩
      have hp':HeavyAnchorDynamics.present s law r σ tape.1 (t.val+1) a:=⟨d,hd,hld⟩
      have hc':=HeavyAnchorDynamics.common_centers s law hr σ tape.1 t hc hd (hlc.trans hld.symm)
      change dist (heavyAnchor _ _ _ _ _ _ _) (heavyAnchor _ _ _ _ _ _ _)≤40*(if _ then r else 0)
      by_cases he:c=d
      · rw [hec,hed,he,dist_self]
        simp
      · have hn:heavyAnchor s law r σ tape.1 t.val a≠heavyAnchor s law r σ tape.1 (t.val+1) a:=by
          rwa [hec,hed]
        rw [ite_eq_left ⟨hp,hp',hn⟩,hec,hed]
        exact (hc'.resolve_left he).2.2.1

lemma common_anchor_distance (t:Fin H) (x y:Y) (a:Key Y k)
    (hx:map s law hr.le σ tape t.val x=a) (hy:map s law hr.le σ tape (t.val+1) y=a):
    dist (anchor s law hr.le σ tape t.val a) (anchor s law hr.le σ tape (t.val+1) a)≤40*r:=
  (common_anchor_motion s law hr σ tape t x y a hx hy).trans
    (mul_le_mul_of_nonneg_left (motion_le s law hr σ tape t.val a) (by norm_num))
end KServer.LevelKeys

end


/-! Cross-time metric rounding uses witnesses only for occupied vertices.
Its anchor surcharge is exactly the already-paid heavy travel. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.JointMetric
open JointExperiment JointAllocation JointHistory
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Y:Type} [MetricSpace Y] [Fintype Y] {k H L:ℕ} [NeZero k]
variable (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
variable {r:Fin L→ℝ} (hr:∀ d,0<r d) (hk:1≤(k:ℝ))

abbrev Node:=PrefixTree.Node (LevelKeys.Key Y k) L
def motion (t:ℕ) (ω:Atom (k:=k) law hr) (d:ℕ) (key:LevelKeys.Key Y k):ℝ:=
  if hd:d<L then LevelKeys.motion s law ω.val.1 (ω.val.2 ⟨d,hd⟩) t key else 0

lemma motion_nonneg (t:ℕ) (ω:Atom (k:=k) law hr) (d:ℕ) (key:LevelKeys.Key Y k):
    0 ≤ motion s law hr t ω d key:=by
  unfold motion
  split_ifs with hd
  · exact LevelKeys.motion_nonneg s law (hr ⟨d,hd⟩) _ _ _ _
  · rfl

lemma anchor_close {R τ:ℝ} (hrad:∀ d,r d=R/τ^(d.val+1)) (t:ℕ) (ω:Atom (k:=k) law hr)
    (d:ℕ) (hd:d<L) (y:Y):
    dist (anchors s law hr t ω d (maps law hr s t ω d y)) y≤20*(R/τ^(d+1)):=by
  simp only [anchors,maps,dite_eq_left hd]
  simpa only [hrad] using LevelKeys.anchor_distance s law (hr ⟨d,hd⟩) ω.val.1 (ω.val.2 ⟨d,hd⟩) t y

lemma anchor_move (t:Fin H) (ω:Atom (k:=k) law hr) (d:ℕ) (hd:d<L) (x y:Y) (key:LevelKeys.Key Y k)
    (hx:maps law hr s t.val ω d x=key) (hy:maps law hr s (t.val+1) ω d y=key):
    dist (anchors s law hr t.val ω d key) (anchors s law hr (t.val+1) ω d key)≤40*motion s law hr t.val ω d key:=by
  simp only [anchors,motion,dite_eq_left hd]
  exact LevelKeys.common_anchor_motion s law (hr ⟨d,hd⟩) ω.val.1 (ω.val.2 ⟨d,hd⟩) t x y key
    (by simpa only [maps,dite_eq_left hd] using hx) (by simpa only [maps,dite_eq_left hd] using hy)

lemma anchor_move_bound {R τ:ℝ} (hrad:∀ d,r d=R/τ^(d.val+1))
    (t:Fin H) (ω:Atom (k:=k) law hr) (d:ℕ) (hd:d<L) (x y:Y) (key:LevelKeys.Key Y k)
    (hx:maps law hr s t.val ω d x=key) (hy:maps law hr s (t.val+1) ω d y=key):
    dist (anchors s law hr t.val ω d key) (anchors s law hr (t.val+1) ω d key)≤40*(R/τ^(d+1)):=by
  refine (anchor_move s law hr t ω d hd x y key hx hy).trans ?_
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  simp only [motion,dite_eq_left hd]
  rw [←hrad ⟨d,hd⟩]
  exact LevelKeys.motion_le s law (hr ⟨d,hd⟩) _ _ _ _

lemma count_witness (t:ℕ) (ω:Atom (k:=k) law hr)
    (c:TreeRounding.Inventory (PrefixTree.tree (LevelKeys.Key Y k) L) k)
    (hc:(PrefixTree.tree (LevelKeys.Key Y k) L).Valid (quota s law hr hk t ω) c.val) (i:Fin k):
    ∃ x,HierarchyCounts.hit (maps law hr s t ω) (PrefixTree.numbering (LevelKeys.Key Y k) L (c.slots _ i)).2 x:=by
  apply PrefixTree.count_witness _ L c (quota s law hr hk t ω) (park_nonneg s law hr hk t ω)
    (PrefixTree.park_le_Q _ L (weight_nonneg law hr) (history law hr) (history_refines law hr)
      (maps law hr s) (hidden law hr s) hk (weight_pos law hr) t ω) hc
  intro v hv
  obtain ⟨x,hx⟩:=PrefixTree.Q_witness _ L (weight_nonneg law hr) (history law hr) (history_refines law hr)
    (maps law hr s) (hidden law hr s) hk (weight_pos law hr) t ω (fun ρ hh=>maps_adapted law hr s t ρ ω hh) v hv
  exact ⟨x,(mem_filter.mp hx).2⟩

lemma motion_sum (t:ℕ) (ω:Atom (k:=k) law hr):
    (∑ v:Node (Y:=Y) (k:=k) (L:=L),park s law hr hk (t+1) ω v*
      PrefixTree.nodeMotion (LevelKeys.Key Y k) L (motion s law hr t ω) v)=JointHeavy.travel s law hr hk t ω:=by
  rw [PrefixTree.nodeMotion_sum]
  unfold JointHeavy.travel
  apply sum_congr rfl
  intro d _
  simp only [motion,dite_eq_left d.isLt,Fintype.sum_sum_type,Fintype.sum_sigma]
  rw [show (∑ i:LevelKeys.Structure k, ∑ a:LevelKeys.Alphabet Y k i,
      LevelKeys.motion s law ω.val.1 (ω.val.2 d) t (Sum.inl ⟨i,a⟩)*
        PrefixTree.bandMass (LevelKeys.Key Y k) L (park s law hr hk (t+1) ω) d.val (Sum.inl ⟨i,a⟩))=
      (∑ a:HeavyLabels.Pool Y, LevelKeys.motion s law ω.val.1 (ω.val.2 d) t (Sum.inl ⟨none,a⟩)*
        PrefixTree.bandMass (LevelKeys.Key Y k) L (park s law hr hk (t+1) ω) d.val (Sum.inl ⟨none,a⟩))+
      ∑ i:LevelKeys.Tier k, ∑ a:LevelKeys.Alphabet Y k (some i),
        LevelKeys.motion s law ω.val.1 (ω.val.2 d) t (Sum.inl ⟨some i,a⟩)*
        PrefixTree.bandMass (LevelKeys.Key Y k) L (park s law hr hk (t+1) ω) d.val (Sum.inl ⟨some i,a⟩) from
    Fintype.sum_option _]
  simp only [LevelKeys.motion,zero_mul,sum_const_zero,add_zero]
  apply sum_congr rfl
  intro a _
  unfold JointHeavy.present JointHeavy.anchor JointHeavy.b JointAllocation.band
  split_ifs
  · rfl
  · exact zero_mul _

lemma count_matching {R τ:ℝ} (hR:0≤R) (hτ:1≤τ) (hdia:∀ x y:Y,dist x y≤R)
    (hrad:∀ d,r d=R/τ^(d.val+1)) (t:Fin H) (ω:Atom (k:=k) law hr)
    (c e:TreeRounding.Inventory (PrefixTree.tree (LevelKeys.Key Y k) L) k)
    (hc:(PrefixTree.tree (LevelKeys.Key Y k) L).Valid (quota s law hr hk t.val ω) c.val)
    (he:(PrefixTree.tree (LevelKeys.Key Y k) L).Valid (quota s law hr hk (t.val+1) ω) e.val):
    matching (PrefixTree.countConfig _ L (s 0) (anchors s law hr t.val ω) c)
      (PrefixTree.countConfig _ L (s 0) (anchors s law hr (t.val+1) ω) e)≤
      120*(∑ v,PrefixTree.weight (LevelKeys.Key Y k) L R τ ((PrefixTree.tree _ L).parent v)*
        |(c.val.subtree v:ℝ)-(e.val.subtree v:ℝ)|)+
      40*(∑ v,(e.val.park v:ℝ)*PrefixTree.nodeMotion _ L (motion s law hr t.val ω) v):=
  PrefixTree.count_matching _ L (s 0) _ _ _ _ _ hR hτ hdia
    (anchor_close s law hr hrad _ ω) (anchor_close s law hr hrad _ ω)
    (anchor_move_bound s law hr hrad t ω) (motion_nonneg s law hr _ ω)
    (anchor_move s law hr t ω) c e (count_witness s law hr hk _ ω c hc) (count_witness s law hr hk _ ω e he)
end KServer.JointMetric

end


/-! A finest-scale singleton region contains the request with quota at least
one. Balanced parks therefore give actual labeled service, not just a marginal
hitting probability. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.JointService
open JointExperiment JointAllocation JointHistory
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Y:Type} [MetricSpace Y] [Fintype Y] {k H L:ℕ} [NeZero k]
variable (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
variable {r:Fin L→ℝ} (hr:∀ d,0<r d) (hk:1≤(k:ℝ))

abbrev Node:=PrefixTree.Node (LevelKeys.Key Y k) L

def leaf (t:ℕ) (ω:Atom (k:=k) law hr) (y:Y):Node (Y:=Y) (k:=k) (L:=L):=
  (PrefixTree.numbering (LevelKeys.Key Y k) L).symm
    ⟨⟨L,Nat.lt_succ_self L⟩,fun i=>maps law hr s t ω i.val y⟩

lemma leaf_number (t:ℕ) (ω:Atom (k:=k) law hr) (y:Y):
    PrefixTree.numbering (LevelKeys.Key Y k) L (leaf s law hr t ω y)=
      ⟨⟨L,Nat.lt_succ_self L⟩,fun i=>maps law hr s t ω i.val y⟩:=
  (PrefixTree.numbering (LevelKeys.Key Y k) L).apply_symm_apply _

lemma leaf_quota (t:Fin H) (ω:Atom (k:=k) law hr):
    1≤quota s law hr hk (t.val+1) ω (leaf s law hr (t.val+1) ω (ω.val.1 t)):=by
  unfold quota PrefixTree.Q
  rw [leaf_number]
  apply HierarchicalQuota.served _ _ _ _ _ hk (weight_pos law hr)
  intro ρ hh
  obtain ⟨i,hi⟩:=hidden_covers law hr s t ρ
  refine ⟨i,?_⟩
  intro d
  rw [hi,request_history law hr t ρ ω hh]
  exact congrFun (congrFun (maps_adapted law hr s _ ρ ω hh) d.val) _

lemma leaf_park (t:ℕ) (ω:Atom (k:=k) law hr) (y:Y):
    park s law hr hk t ω (leaf s law hr t ω y)=quota s law hr hk t ω (leaf s law hr t ω y):=by
  unfold park Rounding.Tree.park
  have he:(PrefixTree.numbering (LevelKeys.Key Y k) L (leaf s law hr t ω y)).1.val=L:=by rw [leaf_number]
  have hs:=PrefixTree.children_sum_leaf (LevelKeys.Key Y k) L (leaf s law hr t ω y)
    (fun v:PrefixTree.Vertex (LevelKeys.Key Y k) L=>quota s law hr hk t ω ((PrefixTree.numbering _ L).symm v)) he
  simp only [OrderIso.symm_apply_apply] at hs
  change quota s law hr hk t ω (leaf s law hr t ω y)-_=quota s law hr hk t ω (leaf s law hr t ω y)
  have hs' : (∑ u:(PrefixTree.travelTree (LevelKeys.Key Y k) L).Child (leaf s law hr t ω y),
      quota s law hr hk t ω u.val)=0:=by exact hs
  rw [hs',sub_zero]

lemma leaf_anchor (hL:0<L) (hf:∀ x y:Y,dist x y≤20*r ⟨L-1,by omega⟩→x=y)
    (t:ℕ) (ω:Atom (k:=k) law hr) (y:Y):
    PrefixTree.nodeAnchor (LevelKeys.Key Y k) L (s 0) (anchors s law hr t ω) (leaf s law hr t ω y)=y:=by
  have hd:PrefixTree.depth (LevelKeys.Key Y k) L (leaf s law hr t ω y)=L:=by
    unfold PrefixTree.depth; rw [leaf_number]
  have hl:PrefixTree.lastKey (LevelKeys.Key Y k) L (leaf s law hr t ω y)=
      some (maps law hr s t ω (L-1) y):=by
    have hh:=congrArg (fun v:PrefixTree.Vertex (LevelKeys.Key Y k) L=>
      if hp:0<v.1.val then some (v.2 ⟨v.1.val-1,by omega⟩) else none)
      (leaf_number s law hr t ω y)
    change PrefixTree.lastKey (LevelKeys.Key Y k) L (leaf s law hr t ω y)=
      (if hp:0<L then some (maps law hr s t ω (L-1) y) else none) at hh
    simpa only [dite_eq_left hL] using hh
  simp only [PrefixTree.nodeAnchor,hl,hd]
  apply hf
  simp only [anchors,maps,dite_eq_left (show L-1<L by omega)]
  exact LevelKeys.anchor_distance s law (hr ⟨L-1,by omega⟩) _ _ _ _

lemma count_serves (hL:0<L) (hf:∀ x y:Y,dist x y≤20*r ⟨L-1,by omega⟩→x=y)
    (t:Fin H) (ω:Atom (k:=k) law hr)
    (c:TreeRounding.Inventory (PrefixTree.tree (LevelKeys.Key Y k) L) k)
    (hc:(PrefixTree.tree (LevelKeys.Key Y k) L).Valid (quota s law hr hk (t.val+1) ω) c.val):
    ∃ i,PrefixTree.countConfig (LevelKeys.Key Y k) L (s 0) (anchors s law hr (t.val+1) ω) c i=ω.val.1 t:=by
  have hp:1≤park s law hr hk (t.val+1) ω (leaf s law hr (t.val+1) ω (ω.val.1 t)):=by
    rw [leaf_park]; exact leaf_quota s law hr hk t ω
  have hi:=TreeRounding.balanced_one_le hp (hc.2.1 (leaf s law hr (t.val+1) ω (ω.val.1 t))).2
  obtain ⟨i,he⟩:=c.slot_exists _ _ (by omega : 0<c.val.park (leaf s law hr (t.val+1) ω (ω.val.1 t)))
  refine ⟨i,?_⟩
  unfold PrefixTree.countConfig
  rw [he]
  exact leaf_anchor s law hr hL hf _ ω _
end KServer.JointService

end

end OAI
