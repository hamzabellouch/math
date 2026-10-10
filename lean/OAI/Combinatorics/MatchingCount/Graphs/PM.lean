import Mathlib
import OAI.Combinatorics.MatchingCount.Sampling.LadderL
import OAI.Combinatorics.MatchingCount.Graphs.MatchingMap

namespace OAI

namespace MatchingFPRAS.Enlargement

open MatchingFPRAS.Switching MatchingFPRAS.Subdivision MatchingFPRAS.RealGeometry
open MatchingFPRAS.Hierarchy MatchingFPRAS.Transport Finset
open MatchingFPRAS.Replica MatchingFPRAS.Replica.Ladder

variable {V : Type*} [Fintype V] [LinearOrder V] [Nontrivial V]

noncomputable local instance (w : V → V → ℝ) (K : ℕ) : DecidableEq (SourceLabel w K) := Classical.decEq _

noncomputable local instance (w : V → V → ℝ) (K : ℕ) : Fintype (BagEdge (sourceBags w K)) := Fintype.ofFinite _

abbrev SourcePM (w : V → V → ℝ) (K : ℕ) := PM (BagEdge.Incident (bags:=sourceBags w K))

noncomputable local instance (w : V → V → ℝ) (K : ℕ) : DecidableEq (SourcePM w K) := Classical.decEq _

omit [Nontrivial V] in
lemma sourceVertex_card_ge (K : ℕ) : Fintype.card V ≤ Fintype.card (SourceVertex V K) := by
  exact Fintype.card_le_of_injective (Sum.inl : V → SourceVertex V K) Sum.inl_injective

theorem source_ladder_sampling (hn : 2 ≤ Fintype.card V)
    (w : V → V → ℝ) (hw : ∀ x y, 0 < w x y) (K : ℕ)
    (hK : ∀ x y, x ≠ y → edgeActivity w x y ≤ (4:ℝ)^K)
    (M₀ : SourcePM w K) (T : ℕ)
    (z : Slot T (ladderQ (Fintype.card (SourceVertex V K)) (sourceD (V:=V) K)) → SourcePM w K)
    (ξ : ℝ) (hξ : 0 < ξ) (hξ1 : ξ < 1) :
    let D := sourceD (V:=V) K
    let N := Fintype.card (SourceVertex V K)
    let wt := sourceBagWeight w K D
    let ν := ladderLaw wt T (ladderQ N D)
    let C := ladderFlow (fun x a ha b hb => sourceBag_tree_adjacent w K hK x a b ha hb) (sourceTree_isTree w K).2 wt T (ladderQ N D)
    (∑ s, |MatchingFPRAS.FiniteChain.walk ν C z (ladderSteps N D K T ξ) s-ν s|)/2 ≤ ξ := by
  classical
  dsimp only
  apply ideal_ladder_sampling (fun x a ha b hb => sourceBag_tree_adjacent w K hK x a b ha hb) (sourceTree_isTree w K).2
    (bagHeight w K) (bagHeight_pos w K) (bagHeight_adjacent w K)
    (sourceD (V:=V) K) K (sourceD_one K) (hn.trans (sourceVertex_card_ge K))
    (sourceBagWeight w K (sourceD (V:=V) K))
    (sourceBagWeight_range w K _ (sourceD_one K) hw hK)
    (sourceBagWeight_global w K _ (sourceD_one K) hw hK) M₀ T z ξ hξ hξ1

end MatchingFPRAS.Enlargement

namespace MatchingFPRAS.Subdivision

open Finset

def probeHoles (p : ℕ) (hp : 1≤p) : Finset (Fin (4*p)) :=
  {⟨2*p-1,by omega⟩,⟨2*p,by omega⟩}

def probeWord (p : ℕ) : Selection (4*p) :=
  fun i => if i.val=2*p then false else alternating true i.val

lemma probeWord_valid (p : ℕ) (hp : 1≤p) : Valid (probeHoles p hp) (probeWord p) := by
  intro i
  by_cases h : i.val=2*p-1 ∨ i.val=2*p
  · have hm : i∈probeHoles p hp := by simpa [probeHoles,Fin.ext_iff] using h
    rw [ite_eq_left hm]
    rcases h with h | h
    · have _hm : i.val%2=1 := by omega
      simp [probeWord,Fin.val_castSucc,Fin.val_succ,h,show 2*p-1+1=2*p by omega,
        alternating,show (2*p-1)%2=1 by omega,show 2*p-1≠2*p by omega]
    · simp [probeWord,Fin.val_castSucc,Fin.val_succ,h,alternating,Nat.add_mod]
  · have hm : i∉probeHoles p hp := by simpa [probeHoles,Fin.ext_iff] using h
    rw [ite_eq_right hm]
    have h₁ : i.val≠2*p := by omega
    have h₂ : i.val+1≠2*p := by omega
    simp only [probeWord,Fin.val_castSucc,Fin.val_succ,ite_eq_right h₁,ite_eq_right h₂,alternating_succ]
    cases alternating true i.val <;> decide

@[simp] lemma probeWord_first (p : ℕ) (hp : 1≤p) : probeWord p 0=true := by
  simp [probeWord,show 0≠2*p by omega]

@[simp] lemma probeWord_last (p : ℕ) (hp : 1≤p) : probeWord p (Fin.last (4*p))=true := by
  simp [probeWord,show 4*p≠2*p by omega,alternating,Nat.mul_mod]

lemma probeHoles_nonempty (p : ℕ) (hp : 1≤p) : (probeHoles p hp).Nonempty := by
  simp [probeHoles]

lemma probeWord_unique (p : ℕ) (hp : 1≤p) (b : Selection (4*p))
    (hb : Valid (probeHoles p hp) b) : b=probeWord p :=
  broken_unique (probeHoles_nonempty p hp) hb (probeWord_valid p hp)

lemma probe_weight (p : ℕ) (B Hu Hv lam : ℝ) :
    selectedWeight (profileActivity p B Hu Hv lam) (probeWord p)=
      (∏ r : Fin p,max B (Hu/2^r.val))*(∏ r : Fin p,max B (Hv/2^r.val)) := by
  have he : selectedWeight (profileActivity p B Hu Hv lam) (probeWord p)=
      selectedWeight (profileActivity p B Hu Hv 1) (fun i => alternating true i.val) := by
    unfold selectedWeight
    apply Finset.prod_congr rfl
    intro i _
    by_cases hi : i.val=2*p
    · have hfi : i=⟨2*p,by omega⟩ := Fin.ext hi
      rw [hfi]
      simp [probeWord,alternating]
    · simp only [probeWord,ite_eq_right hi]
      congr 1
      rcases lt_or_gt_of_ne hi with h | h
      · rw [profile_left _ _ _ _ _ _ h,profile_left _ _ _ _ _ _ h]
      · rw [profile_right _ _ _ _ _ _ h,profile_right _ _ _ _ _ _ h]
  rw [he,exact_profile_weight]
  simp


variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

variable (u v : E → V) (p : ℕ) (hp : 1≤p) (e₀ : E)

def singleProbeHoles (e : E) : Finset (Fin (4*p)) :=
  if e=e₀ then probeHoles p hp else ∅

@[simp] lemma broken_singleProbe : broken (singleProbeHoles p hp e₀)={e₀} := by
  ext e
  by_cases he : e=e₀ <;> simp [singleProbeHoles,he,probeHoles_nonempty]

omit [Fintype V] [Fintype E] [DecidableEq V] in
lemma singleProbe_word (b : E → Selection (4*p))
    (hb : FamilyHoles u v (4*p) ∅ (singleProbeHoles p hp e₀) b) : b e₀=probeWord p := by
  exact probeWord_unique p hp (b e₀) (by simpa [singleProbeHoles] using hb.1 e₀)

lemma residual_singleProbe (b : E → Selection (4*p))
    (hb : FamilyHoles u v (4*p) ∅ (singleProbeHoles p hp e₀) b) :
    residualHoles u v ∅ (singleProbeHoles p hp e₀) b={u e₀,v e₀} := by
  ext x
  simp only [mem_residualHoles,notMem_empty,broken_singleProbe,mem_singleton,
    exists_eq_left,false_or,Uses,singleProbe_word u v p hp e₀ b hb,
    probeWord_first p hp,probeWord_last p hp,true_and,mem_insert,mem_singleton]
  exact or_congr eq_comm eq_comm

def insertProbe (s : E → Bool) (e : E) : Selection (4*p) :=
  if e=e₀ then probeWord p else fun i => alternating (s e) i.val

include hp in
omit [Fintype V] [Fintype E] [DecidableEq V] in
lemma insertProbe_uses (s : E → Bool) (e : E) (x : V) :
    Uses u v (insertProbe p e₀ s) e x ↔
      if e=e₀ then u e₀=x ∨ v e₀=x else s e=true ∧ (u e=x ∨ v e=x) := by
  by_cases he : e=e₀
  · subst e; simp [Uses,insertProbe,probeWord_first p hp,probeWord_last p hp]
  · simp [Uses,insertProbe,he,alternating,and_or_left,Nat.mul_mod]

omit [Fintype V] [Fintype E] in
lemma insertProbe_family (_hne : u e₀≠v e₀) (s : E → Bool)
    (hs : LogicalHoles u v {u e₀,v e₀} {e₀} s) :
    FamilyHoles u v (4*p) ∅ (singleProbeHoles p hp e₀) (insertProbe p e₀ s) := by
  refine ⟨?_,by simp,?_⟩
  · intro e
    by_cases he : e=e₀
    · subst e; simpa [singleProbeHoles,insertProbe] using probeWord_valid p hp
    · simpa [singleProbeHoles,insertProbe,he] using alternating_valid (4*p) (s e)
  · intro x _
    by_cases hx : x∈({u e₀,v e₀} : Finset V)
    · refine ⟨e₀,?_,?_⟩
      · change Uses u v (insertProbe p e₀ s) e₀ x
        rw [insertProbe_uses u v p hp e₀,ite_eq_left rfl]
        simpa only [mem_insert,mem_singleton,eq_comm] using hx
      · intro e he
        by_contra hen
        rw [insertProbe_uses u v p hp e₀,ite_eq_right hen] at he
        exact hs.2.1 x hx e he
    · obtain ⟨e,he,hu⟩ := hs.2.2 x hx
      have he₀ : e≠e₀ := by
        intro h
        subst e
        exact (Bool.noConfusion (he.1.symm.trans (hs.1 e₀ (mem_singleton_self _))))
      refine ⟨e,(insertProbe_uses u v p hp e₀ s e x).mpr (by simpa [he₀] using he),?_⟩
      intro f hf
      by_cases hf₀ : f=e₀
      · subst f
        rw [insertProbe_uses u v p hp e₀,ite_eq_left rfl] at hf
        exact False.elim (hx (by simpa only [mem_insert,mem_singleton,eq_comm] using hf))
      · rw [insertProbe_uses u v p hp e₀,ite_eq_right hf₀] at hf
        exact hu f hf

omit [Fintype V] [DecidableEq V] in
lemma singleProbe_deletionConstant (b : E → Selection (4*p))
    (hb : FamilyHoles u v (4*p) ∅ (singleProbeHoles p hp e₀) b)
    (B Hu Hv lam : E → ℝ) :
    deletionConstant (singleProbeHoles p hp e₀) b
      (fun e => profileActivity p (B e) (Hu e) (Hv e) (lam e))
      (fun e => (∏ r : Fin p,max (B e) (Hu e/2^r.val))*(∏ r : Fin p,max (B e) (Hv e/2^r.val))) =
    ∏ e,(∏ r : Fin p,max (B e) (Hu e/2^r.val))*(∏ r : Fin p,max (B e) (Hv e/2^r.val)) := by
  unfold deletionConstant
  apply Finset.prod_congr rfl
  intro e _
  by_cases he : e=e₀
  · subst e
    simp only [singleProbeHoles,probeHoles_nonempty,ite_true,
      singleProbe_word u v p hp e₀ b hb,probe_weight]
  · simp [singleProbeHoles,he]

theorem singleProbe_partition (hne : u e₀≠v e₀) (B Hu Hv lam : E → ℝ) :
    realHolePartition u v (4*p) ∅ (singleProbeHoles p hp e₀)
      (fun e => profileActivity p (B e) (Hu e) (Hv e) (lam e)) =
    (∏ e,(∏ r : Fin p,max (B e) (Hu e/2^r.val))*(∏ r : Fin p,max (B e) (Hv e/2^r.val))) *
      logicalHolePartition u v {u e₀,v e₀} {e₀} lam := by
  classical
  by_cases h : ∃ b,FamilyHoles u v (4*p) ∅ (singleProbeHoles p hp e₀) b
  · obtain ⟨b,hb⟩ := h
    have hid := deletion_partition_identity (show Even (4*p) from ⟨2*p,by omega⟩)
      u v ∅ (singleProbeHoles p hp e₀) b hb
      (fun e => profileActivity p (B e) (Hu e) (Hv e) (lam e))
      (fun e => List.ofFn fun r : Fin p => max (B e) (Hu e/2^r.val))
      (fun e => (List.ofFn fun r : Fin p => max (B e) (Hv e/2^r.val)).reverse) lam
      (fun e => profileActivity_ofFn p (B e) (Hu e) (Hv e) (lam e))
    simp only [List.prod_reverse,List.prod_ofFn] at hid
    rw [singleProbe_deletionConstant u v p hp e₀ b hb,residual_singleProbe u v p hp e₀ b hb,
      broken_singleProbe] at hid
    exact hid
  · have hl : ¬∃ s,LogicalHoles u v {u e₀,v e₀} {e₀} s := by
      rintro ⟨s,hs⟩
      exact h ⟨insertProbe p e₀ s,insertProbe_family u v p hp e₀ hne s hs⟩
    have hz : realHolePartition u v (4*p) ∅ (singleProbeHoles p hp e₀)
        (fun e => profileActivity p (B e) (Hu e) (Hv e) (lam e))=0 := by
      unfold realHolePartition
      apply Finset.sum_eq_zero
      intro b _
      exact False.elim (h ⟨b.val,b.property⟩)
    have hz' : logicalHolePartition u v {u e₀,v e₀} {e₀} lam=0 := by
      unfold logicalHolePartition
      apply Finset.sum_eq_zero
      intro s _
      exact False.elim (hl ⟨s.val,s.property⟩)
    rw [hz,hz',mul_zero]


end MatchingFPRAS.Subdivision

namespace MatchingFPRAS.Representation

open MatchingFPRAS.Switching MatchingFPRAS.Subdivision MatchingFPRAS.Enlargement Finset

variable {V : Type*} [Fintype V] [LinearOrder V]

omit [Fintype V] in
lemma forbidden_endpoint_redundant (R : Finset V) (e₀ : LogicalEdge V)
    (he : source e₀∈R) (s : LogicalEdge V → Bool) :
    LogicalHoles source target R {e₀} s ↔ LogicalHoles source target R ∅ s := by
  constructor
  · intro h; exact ⟨by simp,h.2⟩
  · intro h
    refine ⟨?_,h.2⟩
    intro e hem
    have heq : e=e₀ := mem_singleton.mp hem
    subst e
    cases hs : s e₀ with
    | false => rfl
    | true => exact False.elim (h.2.1 (source e₀) he e₀ ⟨hs,Or.inl rfl⟩)

lemma logical_partition_redundant (w : V → V → ℝ) (R : Finset V) (e₀ : LogicalEdge V)
    (he : source e₀∈R) :
    logicalHolePartition source target R {e₀} (logicalActivity w)=partition w R := by
  classical
  let := Fintype.ofFinite {s : LogicalEdge V → Bool // LogicalHoles source target R {e₀} s}
  let := Fintype.ofFinite {s : LogicalEdge V → Bool // LogicalHoles source target R ∅ s}
  rw [← logical_partition_eq]
  unfold logicalHolePartition
  apply Fintype.sum_equiv (Equiv.subtypeEquivRight (forbidden_endpoint_redundant R e₀ he))
  intro s
  rfl

end MatchingFPRAS.Representation

namespace MatchingFPRAS.Enlargement

open MatchingFPRAS.Switching MatchingFPRAS.Subdivision MatchingFPRAS.RealGeometry
open MatchingFPRAS.Transport MatchingFPRAS.Representation Finset

variable {V : Type*} [Fintype V] [LinearOrder V] [Nontrivial V]

noncomputable local instance (w : V → V → ℝ) (K : ℕ) : Fintype (BagEdge (sourceBags w K)) := Fintype.ofFinite _

theorem source_probe_partition (w : V → V → ℝ) (K : ℕ) (e₀ : LogicalEdge V) :
    partitionWeight BagEdge.Incident (sourceRealPortion w K)
      (survivors (4*(2*K+2)) ∅ (singleProbeHoles (2*K+2) (by omega) e₀)) =
    (∏ e, pathConstant (2*K+2) (bottleneck w (source e) (target e))
      (sourceHeight w (source e)) (sourceHeight w (target e))) *
        partition w {source e₀,target e₀} := by
  rw [sourceRealPortion_partition]
  change realHolePartition source target (4*(2*K+2)) ∅
    (singleProbeHoles (2*K+2) (by omega) e₀)
    (fun e => profileActivity (2*K+2) (bottleneck w (source e) (target e))
      (sourceHeight w (source e)) (sourceHeight w (target e)) (logicalActivity w e)) = _
  rw [singleProbe_partition _ _ _ _ _ (source_ne_target e₀)]
  rw [logical_partition_redundant w _ e₀ (by simp)]
  rfl

theorem source_probe_ratio (w : V → V → ℝ) (hz : 0<partition w ∅) (K : ℕ)
    (e₀ : LogicalEdge V) (D I : ℝ) :
    (partitionWeight BagEdge.Incident (sourceRealPortion w K)
      (survivors (4*(2*K+2)) ∅ (singleProbeHoles (2*K+2) (by omega) e₀)) / D) /
      (I * partitionWeight BagEdge.Incident (sourceRealPortion w K) univ) =
        holeRatio w {source e₀,target e₀}/(D*I) := by
  rw [source_probe_partition,sourceRealPortion_full w hz]
  have hc : (∏ e : LogicalEdge V, pathConstant (2*K+2) (bottleneck w (source e) (target e))
      (sourceHeight w (source e)) (sourceHeight w (target e)))≠0 := by
    exact ne_of_gt (prod_pos fun e _ => pathConstant_pos _ _ _ _
      (zero_lt_one.trans_le (one_le_bottleneck w _ _)))
  unfold holeRatio
  field_simp

end MatchingFPRAS.Enlargement

end OAI
