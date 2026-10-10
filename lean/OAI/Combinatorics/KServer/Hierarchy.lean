import Mathlib
import OAI.Combinatorics.KServer.OutputRules
import OAI.Combinatorics.KServer.Trees

namespace OAI

/-! Conditional ranks of literal complete-prefix cells, connected to the
allocation's filtered process and compatible lower envelopes. No local
allocation or competitiveness assertion is an input. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.HierarchicalRanks
attribute [local instance] Classical.propDecidable Classical.decEq
open RankTracking PosteriorRanks HierarchyCounts
variable {Ω A Y : Type} [Fintype Ω] [Fintype A] {k d : ℕ}
variable {w : Ω → ℝ} (hw : ∀ ω,0≤w ω)
variable (H : ℕ → Ω → ℕ)
variable (hr : ∀ t ω ρ,H (t+1) ω=H (t+1) ρ → H t ω=H t ρ)
variable (maps : ℕ → Ω → ℕ → Y → A) (q : ℕ → Ω → Fin k → Y)

def family (word : Fin d → A) (a : Fin k) : FilteredRanks w :=
  rankProcess hw H hr (fun t ω=>count (maps t ω) word (q t ω)) a.val

def lower (word : Fin d → A) (z : ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  ∑ a : Fin k, RankFunctions.rank z ((family hw H hr maps q word a).p t ω)

def size (word : Fin d → A) (t : ℕ) (ω : Ω) : ℝ :=
  CoarseProcess.size (family hw H hr maps q word) t ω

omit [Fintype A] in
lemma family_value (word : Fin d → A) (a : Fin k) (t : ℕ) (ω : Ω) :
    (family hw H hr maps q word a).p t ω=
      RankOrder.countRank (conditional w (H t) ω)
        (fun ρ=>count (maps t ρ) word (q t ρ)) a.val :=
  (conditional_rank w (H t) ω _ _).symm

omit [Fintype A] in
lemma lower_eq (word : Fin d → A) (z : ℝ) (t : ℕ) (ω : Ω) :
    lower hw H hr maps q word z t ω=CompatibleBounds.L k (conditional w (H t) ω)
      (fun ρ=>count (maps t ρ) word (q t ρ)) z := by
  simp only [lower,CompatibleBounds.L,family_value]

omit [Fintype A] in
lemma size_eq (word : Fin d → A) (t : ℕ) (ω : Ω) :
    size hw H hr maps q word t ω=CompatibleBounds.M k (conditional w (H t) ω)
      (fun ρ=>count (maps t ρ) word (q t ρ)) := by
  simp only [size,CoarseProcess.size,CompatibleBounds.M,family_value]

lemma lower_superadditive (word : Fin d → A) {z : ℝ}
    (hz : z∈Set.Icc 0 (1/100:ℝ)) (t : ℕ) (ω : Ω) (hω : 0<w ω) :
    (∑ a : A,lower hw H hr maps q (Fin.snoc word a) z t ω) ≤ lower hw H hr maps q word z t ω := by
  simp_rw [lower_eq]
  exact (HierarchyCounts.compatible w hw (H t) ω hω (maps t) word (q t) hz).1

lemma size_superadditive (word : Fin d → A) (t : ℕ) (ω : Ω) (hω : 0<w ω) :
    (∑ a : A,size hw H hr maps q (Fin.snoc word a) t ω) ≤ size hw H hr maps q word t ω := by
  simp_rw [size_eq]
  exact (HierarchyCounts.compatible w hw (H t) ω hω (maps t) word (q t)
    (z:=0) (by norm_num)).2.1

omit [Fintype A] in
lemma family_root (word : Fin 0 → A) (a : Fin k) (t : ℕ) (ω : Ω) :
    (family hw H hr maps q word a).p t ω=0 := by
  change posterior w (H t) (PosteriorRanks.rank _ a.val) ω=0
  have he : PosteriorRanks.rank (fun ρ=>count (maps t ρ) word (q t ρ)) a.val=fun _=>0 := by
    funext ρ
    simp only [PosteriorRanks.rank,count_zero]
    exact ite_eq_right (by omega)
  rw [he]
  simp [posterior,numerator]

omit [Fintype A] in
lemma lower_root (word : Fin 0 → A) (z : ℝ) (t : ℕ) (ω : Ω) :
    lower hw H hr maps q word z t ω=k := by
  simp only [lower,family_root,RankFunctions.rank_zero]
  simp

omit [Fintype A] in
lemma size_root (word : Fin 0 → A) (t : ℕ) (ω : Ω) :
    size hw H hr maps q word t ω=k := by
  simp only [size,CoarseProcess.size,family_root]
  norm_num [RankFunctions.sizeRank]

omit [Fintype A] in
lemma lower_nonneg (word : Fin d → A) {z : ℝ} (hz : z∈Set.Icc 0 (1/100:ℝ))
    (t : ℕ) (ω : Ω) : 0≤lower hw H hr maps q word z t ω :=
  sum_nonneg fun _ _=>RankFunctions.rank_nonneg hz _

omit [Fintype A] in
lemma lower_size (word : Fin d → A) {z : ℝ} (hz : z∈Set.Icc 0 (1/100:ℝ))
    (t : ℕ) (ω : Ω) : lower hw H hr maps q word z t ω ≤36*size hw H hr maps q word t ω := by
  unfold lower size CoarseProcess.size
  rw [mul_sum]
  exact sum_le_sum fun a _=>CompatibleBounds.rank_size_domination hz
    ((family hw H hr maps q word a).range t ω).1

omit [Fintype A] in
lemma size_bound (word : Fin d → A) (t : ℕ) (ω : Ω) : size hw H hr maps q word t ω ≤ k := by
  calc _ ≤ ∑ _a : Fin k,(1:ℝ) := by
        unfold size CoarseProcess.size
        apply sum_le_sum
        intro a _
        have h:=(family hw H hr maps q word a).range t ω
        exact (RankFunctions.sizeRank_le_complement h).trans (by linarith [h.1])
       _ = _ := by simp

omit [Fintype A] in
/-- The first reward rank is exactly zero if each possible hidden placement
has a member in the current observed cell. This is a fiber, not an independence
assertion and does not condition on any rounding outcomes. -/
lemma first_rank_zero {k : ℕ} (hk : 0<k) (q : ℕ → Ω → Fin k → Y)
    (word : Fin d → A) (t : ℕ) (ω : Ω)
    (hs : ∀ ρ,H t ρ=H t ω → ∃ l,hit (maps t ρ) word (q t ρ l)) :
    (family hw H hr maps q word ⟨0,hk⟩).p t ω=0 := by
  change posterior w (H t) (PosteriorRanks.rank _ 0) ω=0
  unfold posterior numerator
  have hn : (∑ ρ∈fiber (H t) (H t ω),w ρ*PosteriorRanks.rank
      (fun z=>count (maps t z) word (q t z)) 0 ρ)=0 := by
    apply sum_eq_zero
    intro ρ hρ
    obtain ⟨l,hl⟩:=hs ρ (mem_filter.mp hρ).2
    have hc : 0<count (maps t ρ) word (q t ρ) := card_pos.mpr ⟨l,by simp [hl]⟩
    simp [PosteriorRanks.rank,not_le.mpr hc]
  rw [hn,zero_div]

omit [Fintype A] in
lemma served_lower {k : ℕ} (hk : 0<k) (q : ℕ → Ω → Fin k → Y)
    (word : Fin d → A) {z : ℝ} (hz : z∈Set.Icc 0 (1/100:ℝ)) (t : ℕ) (ω : Ω)
    (hs : ∀ ρ,H t ρ=H t ω → ∃ l,hit (maps t ρ) word (q t ρ l)) :
    1≤lower hw H hr maps q word z t ω := by
  have h:=single_le_sum (s:=univ)
    (fun a _=>RankFunctions.rank_nonneg hz ((family hw H hr maps q word a).p t ω))
    (mem_univ (⟨0,hk⟩:Fin k))
  rw [first_rank_zero hw H hr maps hk q word t ω hs,RankFunctions.rank_zero] at h
  exact h

end KServer.HierarchicalRanks

end


/-! Actual top-down fractional quotas on all complete-prefix labels. The
parent budget is obtained from conditional count superadditivity, not posited
as an allocation oracle. Fixed unused labels remain present. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.HierarchicalQuota
attribute [local instance] Classical.propDecidable Classical.decEq
open RankTracking ActualStar
variable {Ω A Y:Type} [Fintype Ω] [Fintype A] {k:ℕ} {w:Ω→ℝ}
variable (hw:∀ ω,0≤w ω) (H:ℕ→Ω→ℕ)
variable (hr:∀ t ω ρ,H (t+1) ω=H (t+1) ρ→H t ω=H t ρ)
variable (maps:ℕ→Ω→ℕ→Y→A) (q:ℕ→Ω→Fin k→Y)

def children {d:ℕ} (word:Fin d→A):A→Fin k→FilteredRanks w:=
  fun a=>HierarchicalRanks.family hw H hr maps q (Fin.snoc word a)
def parent {d:ℕ} (word:Fin d→A):Fin k→FilteredRanks w:=
  HierarchicalRanks.family hw H hr maps q word

def quota (hk:1≤(k:ℝ)): (d:ℕ)→(Fin d→A)→ℕ→Ω→ℝ
  | 0,_ ,_,_ => k
  | d+1,word,t,ω=>ActualOutput.out hk (children hw H hr maps q (Fin.init word))
      (parent hw H hr maps q (Fin.init word)) t ω
      (quota hk d (Fin.init word) t ω) (word (Fin.last d))

lemma quota_snoc (hk:1≤(k:ℝ)) {d:ℕ} (word:Fin d→A) (a:A) (t:ℕ) (ω:Ω):
    quota hw H hr maps q hk (d+1) (Fin.snoc word a) t ω=
      ActualOutput.out hk (children hw H hr maps q word) (parent hw H hr maps q word)
        t ω (quota hw H hr maps q hk d word t ω) a:=by
  simp only [quota,Fin.init_snoc,Fin.snoc_last]

lemma sizes {d:ℕ} (word:Fin d→A) (hwpos:∀ ω,0<w ω) (t:ℕ) (ω:Ω):
    (∑ a,CoarseProcess.size (children hw H hr maps q word a) t ω)≤
      CoarseProcess.size (parent hw H hr maps q word) t ω:=
  HierarchicalRanks.size_superadditive hw H hr maps q word t ω (hwpos ω)
omit [Fintype A] in
lemma size_bound {d:ℕ} (word:Fin d→A) (t:ℕ) (ω:Ω):
    CoarseProcess.size (parent hw H hr maps q word) t ω≤k:=
  HierarchicalRanks.size_bound hw H hr maps q word t ω

lemma parent_budget (hk:1≤(k:ℝ)) {d:ℕ} (word:Fin d→A) (hwpos:∀ ω,0<w ω)
    (t:ℕ) (ω:Ω) (x:ℝ) (hx:ActualOutput.lower k (parent hw H hr maps q word) t ω≤x):
    (∑ a,(ActualOutput.n (children hw H hr maps q word) t ω a-
      β k (parent hw H hr maps q word) t ω*ActualOutput.B (children hw H hr maps q word) t ω a+
      ActualOutput.f k (children hw H hr maps q word) (parent hw H hr maps q word) t ω a))≤x:=by
  have hz:=(ActualCaps.ranges hk (parent hw H hr maps q word) t ω (size_bound hw H hr maps q word t ω)).1
  have hs:=HierarchicalRanks.lower_superadditive hw H hr maps q word hz t ω (hwpos ω)
  have heq : (∑ a,(ActualOutput.n (children hw H hr maps q word) t ω a-
      β k (parent hw H hr maps q word) t ω*ActualOutput.B (children hw H hr maps q word) t ω a+
      ActualOutput.f k (children hw H hr maps q word) (parent hw H hr maps q word) t ω a))=
      ∑ a,HierarchicalRanks.lower hw H hr maps q (Fin.snoc word a)
        (ActualCaps.z k (parent hw H hr maps q word) t ω) t ω := by
    apply sum_congr rfl
    intro a _
    exact (TrackedCaps.decomposition (children hw H hr maps q word a)
      (ActualCaps.z k (parent hw H hr maps q word) t ω) t ω).symm
  rw [heq]
  exact hs.trans hx

lemma quota_bounds (hk:1≤(k:ℝ)) (hwpos:∀ ω,0<w ω) (d:ℕ) (word:Fin d→A) (t:ℕ) (ω:Ω):
    ActualOutput.lower k (parent hw H hr maps q word) t ω≤quota hw H hr maps q hk d word t ω ∧
      quota hw H hr maps q hk d word t ω≤72*CoarseProcess.size (parent hw H hr maps q word) t ω:=by
  induction d with
  | zero=>
    have hl:=HierarchicalRanks.lower_root hw H hr maps q word (ActualCaps.z k (parent hw H hr maps q word) t ω) t ω
    have hs:=HierarchicalRanks.size_root hw H hr maps q word t ω
    change ActualOutput.lower k (parent hw H hr maps q word) t ω=(k:ℝ) at hl
    change CoarseProcess.size (parent hw H hr maps q word) t ω=(k:ℝ) at hs
    simp only [quota,hl,hs]
    constructor
    · rfl
    · linarith
  | succ d ih=>
    have hp:=parent_budget hw H hr maps q hk (Fin.init word) hwpos t ω _ (ih (Fin.init word)).1
    have hf:=ActualOutput.out_feasible hk (children hw H hr maps q (Fin.init word))
      (parent hw H hr maps q (Fin.init word)) (sizes hw H hr maps q (Fin.init word) hwpos)
      (size_bound hw H hr maps q (Fin.init word)) t ω _ hp
    have hd:=ActualOutput.output_domination hk (children hw H hr maps q (Fin.init word))
      (parent hw H hr maps q (Fin.init word)) (sizes hw H hr maps q (Fin.init word) hwpos)
      (size_bound hw H hr maps q (Fin.init word)) t ω _ hp (word (Fin.last d))
    have he:Fin.snoc (Fin.init word) (word (Fin.last d))=word:=Fin.snoc_init_self word
    have hl := (hf.1 (word (Fin.last d))).1
    have hu := hd.2
    simp only [children,he] at hl hu
    exact ⟨hl,hu⟩

lemma children_budget (hk:1≤(k:ℝ)) (hwpos:∀ ω,0<w ω) {d:ℕ} (word:Fin d→A) (t:ℕ) (ω:Ω):
    (∑ a,quota hw H hr maps q hk (d+1) (Fin.snoc word a) t ω)≤quota hw H hr maps q hk d word t ω:=by
  simp_rw [quota_snoc]
  exact (ActualOutput.out_feasible hk _ _ (sizes hw H hr maps q word hwpos)
    (size_bound hw H hr maps q word) t ω _ (parent_budget hw H hr maps q hk word hwpos t ω _
      (quota_bounds hw H hr maps q hk hwpos d word t ω).1)).2

lemma quota_nonneg (hk:1≤(k:ℝ)) (hwpos:∀ ω,0<w ω) {d:ℕ} (word:Fin d→A) (t:ℕ) (ω:Ω):
    0≤quota hw H hr maps q hk d word t ω:=
  (ActualOutput.lower_nonneg hk _ t ω (size_bound hw H hr maps q word t ω)).trans
    (quota_bounds hw H hr maps q hk hwpos d word t ω).1

lemma served (hk:1≤(k:ℝ)) (hwpos:∀ ω,0<w ω) {d:ℕ} (word:Fin d→A) (t:ℕ) (ω:Ω)
    (hs:∀ ρ,H t ρ=H t ω→∃ l,HierarchyCounts.hit (maps t ρ) word (q t ρ l)):
    1≤quota hw H hr maps q hk d word t ω:=by
  have hkp:0<k:=by exact_mod_cast (show (0:ℝ)<k by linarith)
  exact (HierarchicalRanks.served_lower hw H hr maps hkp q word
    (ActualCaps.ranges hk _ t ω (size_bound hw H hr maps q word t ω)).1 t ω hs).trans
    (quota_bounds hw H hr maps q hk hwpos d word t ω).1
end KServer.HierarchicalQuota

end

end OAI
