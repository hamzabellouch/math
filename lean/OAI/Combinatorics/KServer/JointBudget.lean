import Mathlib
import OAI.Combinatorics.KServer.PrefixAllocation

namespace OAI

/-! Geometric absorption on the same numbered tree used for metric rounding. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.JointBudget
open JointExperiment JointAllocation HierarchicalQuota ActualCharges RankTracking
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Y:Type} [MetricSpace Y] [Fintype Y] {k H L:ℕ} [NeZero k]
variable (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
variable {r:Fin L→ℝ} (hr:∀ d,0<r d) (hk:1≤(k:ℝ))

abbrev Node:=PrefixTree.Node (LevelKeys.Key Y k) L

def stepQuota (R τ:ℝ) (t:ℕ) (ω:Atom (k:=k) law hr):ℝ:=
  ∑ v:Node (Y:=Y) (k:=k) (L:=L),PrefixTree.weight (LevelKeys.Key Y k) L R τ ((PrefixTree.tree _ L).parent v)*
    |quota s law hr hk (t+1) ω v-quota s law hr hk t ω v|

def stepKey (t:ℕ) (ω:Atom (k:=k) law hr):ℝ:=
  ∑ d:Fin L,r d*keyCross (maps law hr s) (hidden law hr s) d.val t ω

lemma stepQuota_nonneg {R τ:ℝ} (hR:0≤R) (hτ:0≤τ) (t:ℕ) (ω:Atom (k:=k) law hr):
    0 ≤ stepQuota s law hr hk R τ t ω:=by
  unfold stepQuota
  exact sum_nonneg (fun v _=>mul_nonneg (PrefixTree.weight_nonneg _ L hR hτ _) (abs_nonneg _))
lemma stepKey_nonneg (t:ℕ) (ω:Atom (k:=k) law hr):0 ≤ stepKey s law hr t ω:=by
  unfold stepKey keyCross
  exact sum_nonneg fun d _=>mul_nonneg (hr d).le (sum_nonneg fun _ _=>by split_ifs <;> norm_num)

lemma quota_tree {R τ:ℝ} (hτ:τ≠0) (N:ℕ):
    total (weight law hr) N (stepQuota s law hr hk R τ)=
      treeMove (weight_nonneg law hr) (history law hr) (history_refines law hr)
        (maps law hr s) (hidden law hr s) hk (fun d=>R/τ^d) L N:=by
  unfold stepQuota
  rw [ActualCharges.total_sum]
  simp only [total_mul]
  have he:∀ v:Node (Y:=Y) (k:=k) (L:=L),
      PrefixTree.weight (LevelKeys.Key Y k) L R τ ((PrefixTree.tree _ L).parent v)*
        total (weight law hr) N (fun t ω=>|quota s law hr hk (t+1) ω v-quota s law hr hk t ω v|)=
      (τ*(R/τ^(PrefixTree.numbering (LevelKeys.Key Y k) L v).1.val))*
        nodeMove (weight_nonneg law hr) (history law hr) (history_refines law hr)
          (maps law hr s) (hidden law hr s) hk (PrefixTree.numbering (LevelKeys.Key Y k) L v).2 N:=by
    intro v
    by_cases hv:v=0
    · subst v
      have hroot t ω:quota s law hr hk t ω 0=(k:ℝ):=PrefixTree.Q_root _ L _ _ _ _ _ hk t ω
      have hn:=congrArg (fun z:PrefixTree.Vertex (LevelKeys.Key Y k) L=>
        (τ*(R/τ^z.1.val))*nodeMove (weight_nonneg law hr) (history law hr)
          (history_refines law hr) (maps law hr s) (hidden law hr s) hk z.2 N)
        (PrefixTree.numbering_zero (LevelKeys.Key Y k) L)
      rw [hn]
      simp only [hroot,sub_self,abs_zero,nodeMove,PrefixTree.root,Fin.val_zero,HierarchicalQuota.quota,
        total,avg,mul_zero,sum_const_zero]
    · rw [PrefixTree.parent_weight _ L hτ v hv]
      rfl
  simp_rw [he]
  rw [PrefixTree.sum_vertices (LevelKeys.Key Y k) L (fun d word=>
    (τ*(R/τ^d))*nodeMove (weight_nonneg law hr) (history law hr) (history_refines law hr)
      (maps law hr s) (hidden law hr s) hk word N)]
  rw [sum_range_succ']
  have hz:(∑ word:Fin 0→LevelKeys.Key Y k,(τ*(R/τ^0))*
      nodeMove (weight_nonneg law hr) (history law hr) (history_refines law hr)
        (maps law hr s) (hidden law hr s) hk word N)=0:=by
    simp only [nodeMove,HierarchicalQuota.quota,sub_self,abs_zero,total,avg,mul_zero,sum_const_zero]
  rw [hz,add_zero]
  unfold treeMove levelMove
  apply sum_congr rfl
  intro d _
  rw [mul_sum]
  apply sum_congr rfl
  intro word _
  congr 1
  rw [pow_succ]
  field_simp

lemma geo_half {R τ:ℝ} (hR:0≤R) (hτ:2≤τ) (d:ℕ):
    R/τ^(d+1)≤(R/τ^d)/2:=by
  rw [pow_succ,div_mul_eq_div_div]
  exact div_le_div_of_nonneg_left (div_nonneg hR (pow_nonneg (by linarith) _)) (by norm_num) hτ

lemma key_tree {R τ:ℝ} (hτ:τ≠0) (hrad:∀ d,r d=R/τ^(d.val+1)) (N:ℕ):
    keyTransport (w:=weight law hr) (maps law hr s) (hidden law hr s) (fun d=>R/τ^d) L N=
      τ*total (weight law hr) N (stepKey s law hr):=by
  unfold keyTransport stepKey
  simp only [ActualCharges.total_sum,total_mul,mul_sum]
  rw [←Fin.sum_univ_eq_sum_range]
  apply sum_congr rfl
  intro d _
  rw [hrad,←mul_assoc]
  congr 1
  rw [pow_succ]
  field_simp

lemma quota_bound {R τ:ℝ} (hR:0≤R) (hτ:2≤τ) (hrad:∀ d,r d=R/τ^(d.val+1)) (N:ℕ):
    total (weight law hr) N (stepQuota s law hr hk R τ)≤
      (12*τ*localConstant)*ActualCaps.ell k*total (weight law hr) N (stepKey s law hr)+
      2*localConstant*ActualCaps.ell k*treeInventory (LevelKeys.Key Y k) k (fun d=>R/τ^d) L:=by
  have hn:τ≠0:=by linarith
  have hnp:∀ d,0≤R/τ^d:=fun d=>div_nonneg hR (pow_nonneg (by linarith) d)
  rw [quota_tree s law hr hk hn]
  have ha:=allocation_absorption (weight_nonneg law hr) (history law hr) (history_refines law hr)
    (maps law hr s) (hidden law hr s) hk (weight_sum law hr) (weight_pos law hr)
    (fun d=>R/τ^d) hnp (geo_half hR hτ) L N
  have hd:=tree_drift_bound (weight_nonneg law hr) (history law hr) (history_refines law hr)
    (maps law hr s) (hidden law hr s) (fun d=>R/τ^d) hnp (geo_half hR hτ) L N
  rw [key_tree s law hr hn hrad] at hd
  have hc:0≤2*localConstant*ActualCaps.ell k:=by
    have he:=ActualCaps.ell_ge_one hk
    have hl:0≤localConstant:=ActualCharges.output_constants_nonneg.2.2.2.le
    positivity
  exact ha.trans (by nlinarith [mul_le_mul_of_nonneg_left hd hc])

lemma park_bound {R τ:ℝ} (hR:0≤R) (hτ:0<τ) (t:ℕ) (ω:Atom (k:=k) law hr):
    (∑ v:Node (Y:=Y) (k:=k) (L:=L),PrefixTree.weight (LevelKeys.Key Y k) L R τ v*
      |park s law hr hk (t+1) ω v-park s law hr hk t ω v|)≤
      (1+1/τ)*stepQuota s law hr hk R τ t ω:=by
  exact (PrefixTree.travelTree (LevelKeys.Key Y k) L).weighted_park_variation _ _ _
    (PrefixTree.weight_nonneg _ L hR hτ.le)
    ((PrefixTree.Q_root _ L _ _ _ _ _ hk _ _).trans (PrefixTree.Q_root _ L _ _ _ _ _ hk _ _).symm)
    hτ (PrefixTree.parent_weight _ L hτ.ne')
end KServer.JointBudget

end


/-! All-scale, law/horizon-independent roster endpoint, aggregating the actual
chronological edit charges rather than assuming metric distortion. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.EmbeddedCost
open FiniteExperiment TierProcess Pilot LevelKeys LevelLaw LevelRetirement RankTracking
open TierGlobal TierScaleBudget
attribute [local instance] Classical.propDecidable Classical.decEq

lemma exchange {Ω T:Type*} [Fintype Ω] [Fintype T] (w:Ω→ℝ) (r:ℕ→ℝ)
    (S:Finset ℕ) (f:ℕ→T→Ω→ℝ):
    (∑ j∈S,r j*(∑ t:T,avg w (f j t)))=∑ t:T,avg w (fun σ=>∑ j∈S,r j*f j t σ):=by
  simp only [avg,mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro t _
  rw [sum_comm]
  apply sum_congr rfl
  intro σ _
  exact sum_congr rfl (fun j _=>by ring)

variable {Y:Type*} [MetricSpace Y] [Fintype Y] {k H:ℕ} [NeZero k]

def opt (s:Configuration k Y) (law:RequestLaw Y H):ℝ:=
  ∑ σ,law.val σ*optimalCost s (List.ofFn σ)
def inventory (k:ℕ) (r₀ τ:ℝ) (n:ℕ):ℝ:=∑ j∈range n,radius r₀ τ j*(k:ℝ)
def tierMove (s:Configuration k Y) (law:RequestLaw Y H)
    {r₀ τ:ℝ} (hr:0<r₀) (hτ:2 ≤ τ) (n:ℕ):ℝ:=
  ∑ i:Tier k,∑ j∈range n,radius r₀ τ j*(∑ t:Fin H,avg law.val (fun σ=>
    mean (radius r₀ τ j) (fun a=>TierTemporal.editCost s law
      (radius_pos hr (by linarith) j).le σ a t i)))

def tierCoefficient (k:ℕ):ℝ:=147*tierDrift*(1+Real.log ((k:ℝ)+1))+
  98/heavyGamma+32*(1+Real.log k)+31440*Real.log k

lemma tier_all (s:Configuration k Y) (law:RequestLaw Y H)
    {r₀ τ:ℝ} (hr:0<r₀) (hτ:2 ≤ τ) (n:ℕ):
    tierMove s law hr hτ n ≤ tierCoefficient k*opt s law+
      (294+Fintype.card (Tier k))*inventory k r₀ τ n:=by
  have hrad j:0<radius r₀ τ j:=radius_pos hr (by linarith) j
  have hs:=sum_le_sum (s:=univ) (fun i _=>sum_le_sum (s:=range n) (fun j _=>
    mul_le_mul_of_nonneg_left (tier_budget s law (hrad j) i) (hrad j).le))
  simp only [mul_add,sum_add_distrib] at hs
  have hA:=insertion_all s law hr hτ n
  have hB:=far_all s law hr hτ n
  have hC:=noinsert_all s law hr hτ n
  have he:(∑ j∈range n,2*radius r₀ τ j*(k:ℝ))=2*inventory k r₀ τ n:=by
    simp only [inventory,mul_sum,mul_assoc]
  have he':(∑ i:Tier k,∑ j∈range n,radius r₀ τ j*(k:ℝ))=
      (Fintype.card (Tier k):ℝ)*inventory k r₀ τ n:=by simp [inventory]
  rw [he'] at hs
  unfold tierMove tierCoefficient opt
  rw [he] at hA
  linarith
end KServer.EmbeddedCost

end


noncomputable section
open scoped BigOperators
open Finset
namespace KServer.EmbeddedCost
open FiniteExperiment TierProcess Pilot LevelKeys LevelLaw LevelRetirement RankTracking
open TierGlobal TierScaleBudget HeavyTemporal ActualRoster
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Y:Type*} [MetricSpace Y] [Fintype Y] {k H:ℕ} [NeZero k]

def heavyDrift:ℝ:=driftConstant HeavyCenters.template heavyGamma heavyDelta 26

def heavyMove (s:Configuration k Y) (law:RequestLaw Y H)
    {r₀ τ:ℝ} (hr:0<r₀) (hτ:2 ≤ τ) (n:ℕ):ℝ:=
  ∑ j∈range n,radius r₀ τ j*(∑ t:Fin H,avg law.val (fun σ=>
    mean (radius r₀ τ j) (fun a=>HeavyBudget.editCost s law
      (radius_pos hr (by linarith) j).le σ a t)))

def heavyCoefficient (k:ℕ):ℝ:=2*heavyDrift*(1+Real.log ((k:ℝ)+1))+
  2/3+(60/Real.log (1+heavyDelta))*Real.log k

lemma movement_average (s:Configuration k Y) (law:RequestLaw Y H) (c:ℝ):
    (∑ t:Fin H,avg law.val (fun σ=>c*dist (σ t) (hidden s σ t (mover s σ t))))=c*opt s law:=by
  simp only [avg,opt]
  rw [sum_comm,mul_sum]
  apply sum_congr rfl
  intro σ _
  rw [←actual_move_cost s σ]
  simp only [mul_sum]
  exact sum_congr rfl (fun t _=>by ring)

omit [MetricSpace Y] [Fintype Y] [NeZero k] in
lemma far_scales_general {r₀ τ d c:ℝ} (hr:0<r₀) (hτ:2 ≤ τ) (hd:0 ≤ d) (hc:0<c) (n:ℕ):
    (∑ j∈range n,radius r₀ τ j*indicator (c*radius r₀ τ j<d)) ≤ (2/c)*d:=by
  have hb:=radius_truncated_sum hr.le hτ (div_nonneg hd hc.le) n
  refine (sum_le_sum (s:=range n) (fun j _=>?_)).trans (hb.trans_eq (by ring))
  by_cases hj:c*radius r₀ τ j<d
  · have hle:radius r₀ τ j ≤ d/c:=(le_div_iff₀ hc).mpr (by linarith)
    simp only [indicator,ite_eq_left hj,mul_one,ite_eq_left hle,le_refl]
  · simp only [indicator,ite_eq_right hj,mul_zero]
    split_ifs
    · exact (radius_pos hr (by linarith) j).le
    · rfl

lemma nonheavy_scales (s:Configuration k Y) (law:RequestLaw Y H)
    (σ:Fin H→Y) (hσ:0<law.val σ) (t:Fin H) (y:Y)
    {r₀ τ:ℝ} (hr:0<r₀) (hτ:2 ≤ τ) (n:ℕ):
    (∑ j∈range n,radius r₀ τ j*(if heavy s law (radius r₀ τ j) σ t then 0 else dist (σ t) y/radius r₀ τ j)) ≤
      ((60/Real.log (1+heavyDelta))*Real.log k)*dist (σ t) y:=by
  have hb:=mul_le_mul_of_nonneg_right (LevelScale.actual_nonheavy_count s law σ hσ t hr.le hτ n)
    (dist_nonneg (x:=σ t) (y:=y))
  have he:(∑ j∈range n,radius r₀ τ j*(if heavy s law (radius r₀ τ j) σ t then 0 else dist (σ t) y/radius r₀ τ j))=
      (∑ j∈range n,if heavy s law (radius r₀ τ j) σ t then (0:ℝ) else 1)*dist (σ t) y:=by
    rw [sum_mul]
    apply sum_congr rfl
    intro j _
    split_ifs
    · simp
    · field_simp [(radius_pos (τ:=τ) hr (by linarith) j).ne']
  rw [he]
  convert hb using 1 <;> first | rfl | ring

lemma heavy_far_all (s:Configuration k Y) (law:RequestLaw Y H)
    {r₀ τ:ℝ} (hr:0<r₀) (hτ:2 ≤ τ) (n:ℕ):
    (∑ j∈range n,radius r₀ τ j*(∑ t:Fin H,avg law.val (fun σ=>indicator
      (3*radius r₀ τ j<dist (σ t) (hidden s σ t (mover s σ t)))))) ≤ (2/3:ℝ)*opt s law:=by
  rw [exchange]
  refine (sum_le_sum (fun t (_:t∈univ)=>avg_mono law.property.1 (fun σ=>
    far_scales_general hr hτ dist_nonneg (by norm_num : (0:ℝ)<3) n))).trans_eq ?_
  exact movement_average s law (2/3)

lemma heavy_nonheavy_all (s:Configuration k Y) (law:RequestLaw Y H)
    {r₀ τ:ℝ} (hr:0<r₀) (hτ:2 ≤ τ) (n:ℕ):
    (∑ j∈range n,radius r₀ τ j*(∑ t:Fin H,avg law.val (fun σ=>
      if heavy s law (radius r₀ τ j) σ t then 0 else dist (σ t) (hidden s σ t (mover s σ t))/radius r₀ τ j))) ≤
      ((60/Real.log (1+heavyDelta))*Real.log k)*opt s law:=by
  rw [exchange]
  refine le_trans ?_ (movement_average s law _).le
  apply sum_le_sum
  intro t _
  apply sum_le_sum
  intro σ _
  by_cases hs:law.val σ=0
  · simp only [hs,zero_mul,le_refl]
  · exact mul_le_mul_of_nonneg_left (nonheavy_scales s law σ
      (lt_of_le_of_ne (law.property.1 σ) (Ne.symm hs)) t _ hr hτ n) (law.property.1 σ)

lemma heavy_annulus_all (s:Configuration k Y) (law:RequestLaw Y H)
    {r₀ τ:ℝ} (hr:0<r₀) (hτ:2 ≤ τ) (n:ℕ):
    (∑ j∈range n,radius r₀ τ j*(∑ t:Fin H,avg law.val (fun σ=>
      if active s law (radius r₀ τ j) σ t then
      mass (mu s law (t.val+1) σ) (HeavyCenters.annulus (σ t) (radius r₀ τ j)) else 0))) ≤
      heavyDrift*(1+Real.log ((k:ℝ)+1))*opt s law+2*inventory k r₀ τ n:=by
  rw [exchange]
  have hb:=HeavyCenters.annulus_budget s law (γ:=heavyGamma) (δ:=heavyDelta) n 26 hr hτ
    (by norm_num [heavyGamma]) (by norm_num [heavyGamma])
    (by norm_num [heavyDelta]) (by norm_num [heavyDelta])
    (by norm_num [heavyGamma])
  have he:(∑ j∈range n,2*radius r₀ τ j*(k:ℝ))=2*inventory k r₀ τ n:=by
    simp only [inventory,mul_sum,mul_assoc]
  rw [he] at hb
  have hc (t:Fin H) (σ:Fin H→Y) (j:ℕ):
      HeavyCenters.charge s law (radius r₀ τ j) heavyGamma heavyDelta t σ=
        radius r₀ τ j*(if active s law (radius r₀ τ j) σ t then
          mass (mu s law (t.val+1) σ) (HeavyCenters.annulus (σ t) (radius r₀ τ j)) else 0):=by
    unfold HeavyCenters.charge active
    split_ifs <;> ring
  simp_rw [hc] at hb
  exact hb

lemma heavy_all (s:Configuration k Y) (law:RequestLaw Y H)
    {r₀ τ:ℝ} (hr:0<r₀) (hτ:2 ≤ τ) (n:ℕ):
    heavyMove s law hr hτ n ≤ heavyCoefficient k*opt s law+5*inventory k r₀ τ n:=by
  have hrad j:0<radius r₀ τ j:=radius_pos hr (by linarith) j
  have hs:=sum_le_sum (s:=range n) (fun j _=>
    mul_le_mul_of_nonneg_left (HeavyBudget.heavy_budget s law (hrad j)) (hrad j).le)
  have hA:=heavy_annulus_all s law hr hτ n
  have hB:=heavy_far_all s law hr hτ n
  have hC:=heavy_nonheavy_all s law hr hτ n
  simp only [mul_add,sum_add_distrib] at hs
  have he:(∑ j∈range n,radius r₀ τ j*(2*(∑ t:Fin H,avg law.val (fun σ=>
      if active s law (radius r₀ τ j) σ t then
      mass (mu s law (t.val+1) σ) (HeavyCenters.annulus (σ t) (radius r₀ τ j)) else 0))))=
      2*(∑ j∈range n,radius r₀ τ j*(∑ t:Fin H,avg law.val (fun σ=>
      if active s law (radius r₀ τ j) σ t then
      mass (mu s law (t.val+1) σ) (HeavyCenters.annulus (σ t) (radius r₀ τ j)) else 0))):=by
    rw [mul_sum]
    exact sum_congr rfl (fun j _=>by ring)
  rw [he] at hs
  change heavyMove s law hr hτ n ≤ _+inventory k r₀ τ n at hs
  unfold heavyCoefficient
  linarith
end KServer.EmbeddedCost

end


/-! The chronological triangle inequality for the literal priority stages. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.PriorityKeys
attribute [local instance] Classical.propDecidable Classical.decEq
open ActualRoster

lemma indicator_triangle {B:Type*} (a b c:B):
    indicator (a≠c) ≤ indicator (a≠b)+indicator (b≠c):=by
  by_cases hab:a=b
  · subst b; simp [indicator]
  · by_cases hbc:b=c
    · subst c; simp [indicator]
    · unfold indicator
      simp only [ite_eq_left hab,ite_eq_left hbc]
      split_ifs <;> norm_num

lemma indicator_chain {B:Type*} (f:ℕ→B) (n:ℕ):
    indicator (f 0≠f n) ≤ ∑ j∈range n,indicator (f j≠f (j+1)):=by
  induction n with
  | zero=>simp [indicator]
  | succ n ih=>
    rw [sum_range_succ]
    exact (indicator_triangle (f 0) (f n) (f (n+1))).trans (add_le_add ih (le_refl _))

variable {I Y:Type*} [Fintype I] [LinearOrder I] {A:I→Type*}

lemma stages_total (q₀ q₁:(i:I)→Y→Option (A i)) (x:Y):
    indicator (key q₀ x≠key q₁ x) ≤
      ∑ j:I,indicator (key (stageBefore q₀ q₁ j) x≠key (stageAfter q₀ q₁ j) x):=by
  let m:=Fintype.card I
  let e:Fin m ≃o I:=Fintype.orderIsoFinOfCardEq I rfl
  let blend (n:ℕ):(i:I)→Y→Option (A i):=fun i=>if (e.symm i).val<n then q₁ i else q₀ i
  have hzero:blend 0=q₀:=by funext i; simp [blend]
  have hlast:blend m=q₁:=by funext i; simp [blend,(e.symm i).isLt]
  have hbefore (j:Fin m):blend j.val=stageBefore q₀ q₁ (e j):=by
    funext i
    have he:(e.symm i).val<j.val ↔ i<e j:=by
      change e.symm i<j ↔ i<e j
      constructor
      · intro h; simpa only [e.apply_symm_apply] using e.strictMono h
      · intro h; simpa only [e.symm_apply_apply] using e.symm.strictMono h
    simp only [blend,stageBefore,he]
  have hafter (j:Fin m):blend (j.val+1)=stageAfter q₀ q₁ (e j):=by
    funext i
    have he:(e.symm i).val<j.val+1 ↔ i≤e j:=by
      rw [Nat.lt_succ_iff]
      change e.symm i≤j ↔ i≤e j
      constructor
      · intro h; simpa only [e.apply_symm_apply] using e.monotone h
      · intro h; simpa only [e.symm_apply_apply] using e.symm.monotone h
    simp only [blend,stageAfter,he]
  have hb:=indicator_chain (fun n=>key (blend n) x) m
  rw [hzero,hlast,←Fin.sum_univ_eq_sum_range] at hb
  simp only [hbefore,hafter] at hb
  exact hb.trans_eq (Fintype.sum_equiv e.toEquiv _ _ (fun _=>rfl))
end KServer.PriorityKeys

end


/-! The all-step embedded motion of the selected hidden labeled optimum. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.EmbeddedCost
open FiniteExperiment TierProcess Pilot LevelKeys LevelLaw LevelRetirement RankTracking
open ActualRoster RankTracking TierTemporal
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Y:Type*} [MetricSpace Y] [Fintype Y] {k H:ℕ} [NeZero k]

omit [MetricSpace Y] [Fintype Y] [NeZero k] in
lemma indicator_ne_comm {B:Type*} (a b:B):indicator (a≠b)=indicator (b≠a):=by
  simp only [ne_comm]

lemma map_edit (s:Configuration k Y) (law:RequestLaw Y H) {r:ℝ} (hr:0≤r)
    (σ:Fin H→Y) (a:Tape Y k H r) (t:ℕ) (p:Y):
    indicator (map s law hr σ a t p≠map s law hr σ a (t+1) p) ≤
      HeavyTemporal.charge s law hr σ a t p+
        ∑ i:Tier k,LevelTierEdits.charge s law hr σ a t i p:=by
  have hb:=PriorityKeys.stages_total (keys s law hr σ a t) (keys s law hr σ a (t+1)) p
  let f (j:Structure k):ℝ:=indicator
    (PriorityKeys.key (PriorityKeys.stageBefore (keys s law hr σ a t) (keys s law hr σ a (t+1)) j) p≠
      PriorityKeys.key (PriorityKeys.stageAfter (keys s law hr σ a t) (keys s law hr σ a (t+1)) j) p)
  change _ ≤ ∑ j:Structure k,f j at hb
  let e:Structure k ≃ Option (Tier k):=Equiv.refl _
  rw [Fintype.sum_equiv e f (fun j=>f (e.symm j)) (fun _=>rfl),Fintype.sum_option] at hb
  exact hb

def mappedCross (s:Configuration k Y) (law:RequestLaw Y H) {r:ℝ} (hr:0≤r)
    (σ:Fin H→Y) (a:Tape Y k H r) (t:Fin H):ℝ:=
  ∑ l:Fin k,indicator (map s law hr σ a t (hidden s σ t l)≠
    map s law hr σ a (t.val+1) (hidden s σ (t.val+1) l))

lemma physical_cross (s:Configuration k Y) (law:RequestLaw Y H) {r:ℝ} (hr:0≤r)
    (σ:Fin H→Y) (a:Tape Y k H r) (t:Fin H):
    (∑ l:Fin k,indicator (map s law hr σ a (t.val+1) (hidden s σ t l)≠
      map s law hr σ a (t.val+1) (hidden s σ (t.val+1) l)))=
        indicator (map s law hr σ a (t.val+1) (σ t)≠
          map s law hr σ a (t.val+1) (hidden s σ t (mover s σ t))):=by
  rw [hidden_step]
  rw [sum_eq_single (mover s σ t)]
  · simp only [serve,Function.update_self]
    exact indicator_ne_comm _ _
  · intro l _ hl
    simp [serve,Function.update_of_ne hl,indicator]
  · simp

lemma mapped_step (s:Configuration k Y) (law:RequestLaw Y H) {r:ℝ} (hr:0≤r)
    (σ:Fin H→Y) (a:Tape Y k H r) (t:Fin H):
    mappedCross s law hr σ a t ≤ HeavyBudget.editCost s law hr σ a t+
      (∑ i:Tier k,TierTemporal.editCost s law hr σ a t i)+
      indicator (map s law hr σ a (t.val+1) (σ t)≠
        map s law hr σ a (t.val+1) (hidden s σ t (mover s σ t))):=by
  have hs:=sum_le_sum (s:=univ) (fun l (_:l∈univ)=>
    (PriorityKeys.indicator_triangle (map s law hr σ a t (hidden s σ t l))
      (map s law hr σ a (t.val+1) (hidden s σ t l))
      (map s law hr σ a (t.val+1) (hidden s σ (t.val+1) l))).trans
        (add_le_add (map_edit s law hr σ a t (hidden s σ t l)) (le_refl _)))
  simp only [sum_add_distrib] at hs
  rw [physical_cross] at hs
  unfold mappedCross HeavyBudget.editCost TierTemporal.editCost
  exact hs.trans_eq (by rw [sum_comm (f:=fun l i=>LevelTierEdits.charge s law hr σ a t i (hidden s σ t l))])

lemma mapped_step_mean (s:Configuration k Y) (law:RequestLaw Y H) {r:ℝ} (hr:0<r)
    (σ:Fin H→Y) (t:Fin H):
    mean r (fun a=>mappedCross s law hr.le σ a t) ≤
      mean r (fun a=>HeavyBudget.editCost s law hr.le σ a t)+
      (∑ i:Tier k,mean r (fun a=>TierTemporal.editCost s law hr.le σ a t i))+
      LevelSpatial.separation s law hr.le σ (t.val+1) (σ t) (hidden s σ t (mover s σ t)):=by
  have hb:=mean_mono hr (fun a=>mapped_step s law hr.le σ a t)
  simp only [mean_add,mean_sum] at hb
  have he:mean r (fun a=>indicator (map s law hr.le σ a (t.val+1) (σ t)≠
      map s law hr.le σ a (t.val+1) (hidden s σ t (mover s σ t))))=
      LevelSpatial.separation s law hr.le σ (t.val+1) (σ t) (hidden s σ t (mover s σ t)):=by
    rw [mean_indicator]
    unfold LevelSpatial.separation
    apply sum_congr rfl
    intro a _
    split_ifs <;> rfl
  rw [he] at hb
  exact hb

end KServer.EmbeddedCost

end


/-! The finite all-scale offline embedding endpoint. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.EmbeddedCost
open FiniteExperiment TierProcess Pilot LevelKeys LevelLaw LevelRetirement RankTracking
open ActualRoster RankTracking TierTemporal
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Y:Type*} [MetricSpace Y] [Fintype Y] {k H:ℕ} [NeZero k]

def spatialCoefficient (k:ℕ):ℝ:=8+1050*(60/Real.log (1+heavyDelta)+60)*Real.log k

def spatialMove (s:Configuration k Y) (law:RequestLaw Y H)
    {r₀ τ:ℝ} (hr:0<r₀) (hτ:2≤τ) (n:ℕ):ℝ:=
  ∑ j∈range n,radius r₀ τ j*(∑ t:Fin H,avg law.val (fun σ=>
    LevelSpatial.separation s law (radius_pos hr (by linarith) j).le σ (t.val+1)
      (σ t) (hidden s σ t (mover s σ t))))

lemma spatial_all (s:Configuration k Y) (law:RequestLaw Y H)
    {r₀ τ:ℝ} (hr:0<r₀) (hτ:2≤τ) (n:ℕ):
    spatialMove s law hr hτ n ≤ spatialCoefficient k*opt s law:=by
  unfold spatialMove
  rw [exchange]
  refine le_trans ?_ (movement_average s law _).le
  apply sum_le_sum
  intro t _
  apply sum_le_sum
  intro σ _
  by_cases hs:law.val σ=0
  · simp only [hs,zero_mul,le_refl]
  · exact mul_le_mul_of_nonneg_left (LevelSpatial.spatial_sum s law σ
      (lt_of_le_of_ne (law.property.1 σ) (Ne.symm hs)) t _ hr hτ n) (law.property.1 σ)

def keyMove (s:Configuration k Y) (law:RequestLaw Y H)
    {r₀ τ:ℝ} (hr:0<r₀) (hτ:2≤τ) (n:ℕ):ℝ:=
  ∑ j∈range n,radius r₀ τ j*(∑ t:Fin H,avg law.val (fun σ=>
    mean (radius r₀ τ j) (fun a=>mappedCross s law
      (radius_pos hr (by linarith) j).le σ a t)))

lemma key_move_decompose (s:Configuration k Y) (law:RequestLaw Y H)
    {r₀ τ:ℝ} (hr:0<r₀) (hτ:2≤τ) (n:ℕ):
    keyMove s law hr hτ n ≤ heavyMove s law hr hτ n+tierMove s law hr hτ n+
      spatialMove s law hr hτ n:=by
  have hrad j:0<radius r₀ τ j:=radius_pos hr (by linarith) j
  have hs:=sum_le_sum (s:=range n) (fun j _=>mul_le_mul_of_nonneg_left
    (sum_le_sum (s:=univ) (fun t (_:t∈univ)=>avg_mono law.property.1 (fun σ=>
      mapped_step_mean s law (hrad j) σ t))) (hrad j).le)
  simp only [avg_add,avg_sum,mul_add,sum_add_distrib] at hs
  have he:(∑ j∈range n,radius r₀ τ j*(∑ t:Fin H,∑ i:Tier k,avg law.val (fun σ=>
      mean (radius r₀ τ j) (fun a=>TierTemporal.editCost s law (hrad j).le σ a t i))))=
        tierMove s law hr hτ n:=by
    unfold tierMove
    simp_rw [sum_comm (f:=fun t i=>avg law.val (fun σ=>
      mean (radius r₀ τ _) (fun a=>TierTemporal.editCost s law (hrad _).le σ a t i)))]
    simp only [mul_sum]
    rw [sum_comm]
  rw [he] at hs
  exact hs

lemma embedding_all (s:Configuration k Y) (law:RequestLaw Y H)
    {r₀ τ:ℝ} (hr:0<r₀) (hτ:2≤τ) (n:ℕ):
    keyMove s law hr hτ n ≤
      (tierCoefficient k+heavyCoefficient k+spatialCoefficient k)*opt s law+
        (299+Fintype.card (Tier k))*inventory k r₀ τ n:=by
  have hD:=key_move_decompose s law hr hτ n
  have hA:=tier_all s law hr hτ n
  have hB:=heavy_all s law hr hτ n
  have hC:=spatial_all s law hr hτ n
  linarith

end KServer.EmbeddedCost

end


/-! The finite all-scale embedding is used with the reversed geometric list
of radii in the top-down prefix construction, not with a moved quantifier. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.JointEmbedding
open JointExperiment RankTracking ActualCharges
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Y:Type} [MetricSpace Y] [Fintype Y] {k H L:ℕ} [NeZero k]
variable (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
variable {r:Fin L→ℝ} (hr:∀ d,0<r d)

def scaleCost (a:ℝ):ℝ:=if ha:0<a then
  ∑ t:Fin H,avg law.val (fun σ=>LevelRetirement.mean a (fun tape=>
    EmbeddedCost.mappedCross s law ha.le σ tape t)) else 0

lemma cross_mean (d:Fin L) (t:Fin H):
    avg (weight law hr) (HierarchicalQuota.keyCross (maps law hr s) (hidden law hr s) d.val t.val)=
      avg law.val (fun σ=>LevelRetirement.mean (r d) (fun tape=>
        EmbeddedCost.mappedCross s law (hr d).le σ tape t)):=by
  have he:(HierarchicalQuota.keyCross (maps law hr s) (hidden law hr s) d.val t.val)=
      fun ω:Atom (k:=k) law hr=>EmbeddedCost.mappedCross s law (hr d).le ω.val.1 (ω.val.2 d) t:=by
    funext ω
    unfold HierarchicalQuota.keyCross EmbeddedCost.mappedCross
    simp only [JointExperiment.maps,dite_eq_left d.isLt,JointExperiment.hidden]
    apply sum_congr rfl
    intro i _
    unfold ActualRoster.indicator
    split_ifs <;> simp_all only [ne_eq,eq_comm,not_true_eq_false,not_false_eq_true]
  rw [he]
  exact scale_mean law hr d (fun σ tape=>EmbeddedCost.mappedCross s law (hr d).le σ tape t)

lemma total_key:
    total (weight law hr) H (JointBudget.stepKey s law hr)=∑ d:Fin L,r d*scaleCost s law (r d):=by
  unfold total JointBudget.stepKey
  rw [←Fin.sum_univ_eq_sum_range]
  simp only [avg_sum,avg_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro d _
  rw [←mul_sum]
  simp_rw [cross_mean s law hr d]
  rw [scaleCost,dite_eq_left (hr d)]

lemma hidden_cost:
    total (weight law hr) H (fun t ω=>∑ i:Fin k,dist (hidden law hr s t ω i) (hidden law hr s (t+1) ω i))=
      EmbeddedCost.opt s law:=by
  unfold total
  rw [←Fin.sum_univ_eq_sum_range,←avg_sum]
  unfold JointExperiment.hidden
  rw [avg_raw law hr (fun z:Raw Y k H L r =>∑ t:Fin H,∑ i:Fin k,
    dist (FiniteExperiment.hidden s z.1 t.val i) (FiniteExperiment.hidden s z.1 (t.val+1) i))]
  exact FiniteExperiment.expected_hidden_cost s law (tapeLaw hr)

lemma radius_reverse {R τ:ℝ} (hτ:τ≠0) (d:Fin L):
    R/τ^(d.val+1)=Pilot.radius (R/τ^L) τ d.rev.val:=by
  unfold Pilot.radius
  have hd:d.rev.val+(d.val+1)=L:=by simp only [Fin.val_rev]; omega
  apply (div_eq_iff (pow_ne_zero _ hτ)).mpr
  rw [mul_assoc,←pow_add,hd,div_mul_cancel₀ _ (pow_ne_zero _ hτ)]

lemma key_bound {R τ:ℝ} (hR:0<R) (hτ:2≤τ) (hrad:∀ d,r d=R/τ^(d.val+1)):
    total (weight law hr) H (JointBudget.stepKey s law hr)≤
      (EmbeddedCost.tierCoefficient k+EmbeddedCost.heavyCoefficient k+EmbeddedCost.spatialCoefficient k)*
        EmbeddedCost.opt s law+
      (299+Fintype.card (LevelKeys.Tier k))*EmbeddedCost.inventory k (R/τ^L) τ L:=by
  have ht:0<τ:=by linarith
  have hbase:0<R/τ^L:=div_pos hR (pow_pos ht _)
  have he:total (weight law hr) H (JointBudget.stepKey s law hr)=
      EmbeddedCost.keyMove s law hbase hτ L:=by
    rw [total_key]
    simp_rw [hrad, radius_reverse ht.ne']
    rw [Fintype.sum_equiv Fin.revPerm
      (fun d:Fin L=>Pilot.radius (R/τ^L) τ d.rev.val*scaleCost s law (Pilot.radius (R/τ^L) τ d.rev.val))
      (fun d:Fin L=>Pilot.radius (R/τ^L) τ d.val*scaleCost s law (Pilot.radius (R/τ^L) τ d.val)) (fun _=>rfl)]
    rw [Fin.sum_univ_eq_sum_range (fun j=>Pilot.radius (R/τ^L) τ j*
      scaleCost s law (Pilot.radius (R/τ^L) τ j)) L]
    unfold EmbeddedCost.keyMove
    apply sum_congr rfl
    intro d _
    rw [scaleCost,dite_eq_left (Pilot.radius_pos hbase ht d)]
  rw [he]
  exact EmbeddedCost.embedding_all s law hbase hτ L
end KServer.JointEmbedding

end

end OAI
