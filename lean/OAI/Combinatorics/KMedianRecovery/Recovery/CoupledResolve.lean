import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.CoupledFinish
import OAI.Combinatorics.KMedianRecovery.Recovery.CoupledLeaf

namespace OAI

namespace MetricKMedianRecovery.CanonicalCoupledMerge

section
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion PhaseMergeRefinement PhaseCountCrossing
  CanonicalMergeCrossing RationalLeaves PhaseMergeInvariant PhaseCoupledMerge CanonicalLengthView
variable {V : Type*} [LinearOrder V] {d : ℕ}

abbrev Outcome (V : Type*) := Output V ⊕ State V

def resolve (loc : Fin d → V) (distance : V → Fin d → ℚ) (F : Finset V)
    (v M : ℚ) (N precision q n k key : ℕ) (B : Finset (Label V)) (lam : ℚ)
    (P : List (List (Label V))) : CanonicalMergeCrossing.Result (Label V) → Outcome V
  | .success H T => .inl (finish B lam (P++[H]) T)
  | .common H T U => .inr (sameState B lam (P++[H]) T U)
  | .sensitive H G T U =>
    match view (rows distance) (F.image original) ((F.sort (·≤·)).map original) H G with
    | none => .inl (finish B lam P [])
    | some J =>
      let i := parent J.root
      let C := J.common H
      match CanonicalSensitiveEndpoint.run loc distance F (after ∅ P) v lam (20*N*M) q n k key precision H T U J with
      | .success s W => .inl (finish (insert (leaf key i s) B) lam (P++[C++[leaf key i s]]) W)
      | .bracket l u A Z => .inr (leafState B P lam key i C l u A Z)

variable [PseudoMetricSpace V]
attribute [local instance] RationalLeaves.metric

def Outcome.Correct (loc : Fin d → V) (F : Finset V) (v eta lo hi : ℝ) (q n k : ℕ) : Outcome V → Prop
  | .inl o => o.Correct loc F v eta lo hi (q+(n+1)) k
  | .inr s => Certified loc F v eta lo hi (q+1) n k s

lemma resolve_correct (loc : Fin d → V) (distance : V → Fin d → ℚ)
    (hmetric : ∀ x j,(distance x j:ℝ)=dist x (loc j))
    (F : Finset V) (v M : ℚ) (eta lo hi : ℝ) (N precision q n k key : ℕ)
    (B : Finset (Label V)) (lam : ℚ) (P : List (List (Label V)))
    (hF : F.Nonempty) (hM : 0<M) (hN : 3≤N) (hB : Before key B) (hkey : key<3*(q+1))
    (hv : (0:ℝ)<(v:ℝ)) (hv1 : (v:ℝ)<1/6) (hlam : (0:ℝ)<(lam:ℝ)) (heta : 0≤eta)
    (hdis : Disjoint (F.image original) B) (hl : lo≤(lam:ℝ)) (hu : (lam:ℝ)≤hi)
    (hlamUpper : (lam:ℝ)≤8*N*(M:ℝ)) (hprecision : (1/(2:ℚ)^precision:ℚ)≤eta)
    (hdiam : ∀ i∈F,∀ j,dist i (loc j)≤(M:ℝ))
    (hp : PrefixData (fun j=>original (loc j)) (F.image original) B v lam eta q P)
    (R : CanonicalMergeCrossing.Result (Label V))
    (hR : R.Correct (fun j=>original (loc j)) (F.image original) B (after ∅ P) v lam eta q n k) :
    (resolve loc distance F v M N precision q n k key B lam P R).Correct loc F v eta lo hi q n k := by
  have hfinish : ∀ (H : List (Label V)) (T : List (List (Label V))),
      Good (fun j=>original (loc j)) (F.image original) B (after ∅ P) v ((1+(v:ℝ)^2)^q) lam eta H →
      Runs (fun j=>original (loc j)) (F.image original) B (after ∅ P∪H.toFinset) v lam (q+1) n T →
      finalCount (F.image original) (after ∅ P) H T=k →
      (finish B lam (P++[H]) T).Correct loc F v eta lo hi (q+(n+1)) k := by
    intro H T hH hT hc
    have hpn := hp.append_phase hv hv1 hlam H hH.1 (hH.2.trans (by omega))
    have hh := finish_correct hpn hv hv1 hlam heta hdis hl hu
      (T:=T) (n:=n) (by simpa only [after_append,after] using hT)
      (by simpa only [after_append,after,finalCount] using hc)
    simpa only [Nat.add_assoc,Nat.add_comm 1 n] using hh
  cases R with
  | success H T =>
    exact hfinish H T hR.1 hR.2.1 hR.2.2
  | common H T U =>
    obtain ⟨hH,hT,hU,hs⟩ := hR
    apply same_certified (hB.mono (by omega)) heta hdis hl hu
      (hp.append_phase hv hv1 hlam H hH.1 (hH.2.trans (by omega)))
    · simpa only [after_append,after] using hT
    · simpa only [after_append,after] using hU
    · simpa only [after_append,after,finalCount] using hs
  | sensitive H G T U =>
    obtain ⟨hH,hG,he,hT,hU,hs⟩ := hR
    obtain ⟨J,hJ⟩ := view_exists (fun j=>original (loc j)) (rows distance) (rows_spec loc distance hmetric)
      (F.image original) B ((F.sort (·≤·)).map original) H G
      (fun i hi=>by
        obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hi
        exact List.mem_map.mpr ⟨j,by simpa only [Finset.mem_sort] using hj,rfl⟩) hdis he
    have ha := view_sound (rows distance) (F.image original) ((F.sort (·≤·)).map original) H G J hJ
    have hNr : (0:ℚ)<N := by exact_mod_cast (show 0<N by omega)
    have hb : (0:ℚ)<20*N*M := by positivity
    have hE := CanonicalSensitiveEndpoint.endpoints loc distance hmetric F B (after ∅ P)
      v lam eta M q n k key N (20*N*M) H G T U J hF hB hp.after_subset hdis hv hv1 hlam
      (by exact_mod_cast hM) hN hlamUpper (by push_cast; rfl) hdiam hp.row hH hG hT hU ha hs
    have hc := CanonicalSensitiveEndpoint.run_spec loc distance hmetric F B (after ∅ P) v lam (20*N*M) eta
      q n k key precision H T U J hp.after_subset hv hv1 hb hE
    have hC := hE.1
    dsimp only [resolve]
    rw [hJ]
    dsimp only
    cases hr : CanonicalSensitiveEndpoint.run loc distance F (after ∅ P) v lam (20*N*M) q n k key precision H T U J with
    | success x W =>
      rw [hr] at hc
      obtain ⟨_,_,hW,hcount⟩ := hc
      have hpn := prefix_leaf hp key hB (parent J.root) x hv hv1 hlam (J.common H) hC
      have hd' : Disjoint (F.image original) (insert (leaf key (parent J.root) x) B) := by
        rw [Finset.disjoint_insert_right]
        exact ⟨fun he=>fresh F B key hB (parent J.root) x (Finset.mem_union_left _ he),hdis⟩
      have hbdy : after ∅ (P++[J.common H++[leaf key (parent J.root) x]])=
          insert (leaf key (parent J.root) x) (after ∅ P∪(J.common H).toFinset) := by
        simp only [after_append,after,List.toFinset_append,List.toFinset_cons,List.toFinset_nil,Finset.union_insert,Finset.union_empty]
      have hh := finish_correct hpn hv hv1 hlam heta hd' hl hu (T:=W) (n:=n) (k:=k)
        (by simpa only [hbdy] using hW) (by simpa only [hbdy] using hcount)
      simpa only [Outcome.Correct,Nat.add_assoc,Nat.add_comm 1 n] using hh
    | bracket l u A Z =>
      rw [hr] at hc
      obtain ⟨hl0,hlu,_,hw,hA,hZ,hAZ⟩ := hc
      apply leaf_certified hp key hB hkey (parent J.root) (J.common H) l u A Z hv hv1 hlam hdis hl hu hC hl0 hlu _ hA hZ hAZ
      have hh : ((u-l:ℚ):ℝ)≤((1/(2:ℚ)^precision:ℚ):ℝ) := by exact_mod_cast hw
      simpa only [Rat.cast_sub] using hh.trans hprecision

end

open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion PhaseMergeRefinement PhaseCountCrossing
  CanonicalMergeCrossing RationalLeaves PhaseMergeInvariant PhaseCoupledMerge
variable {V : Type*} [LinearOrder V] {d : ℕ}

def banks (F : Finset V) (B : Finset (Label V)) (q : ℕ) : Finset (Label V) :=
  PhaseMergePath.pool (F.image original) (PhaseMergePath.pool (F.image original) B (copy (3*q))) (copy (3*q+1))

def step (loc : Fin d → V) (distance : V → Fin d → ℚ) (F : Finset V)
    (v M : ℚ) (N precision q n k : ℕ) (s : State V) : Outcome V :=
  match s.T,s.U with
  | H::T,G::U =>
    let W := FiniteLabelContinuation.continuation (fun j=>original (loc j)) (rows distance)
      (F.image original) v s.lam' (q+1) n (after ∅ s.mapPrefix∪G.toFinset)
    let c := finalCount (F.image original) (after ∅ s.mapPrefix) G W
    if c=k then .inl (finish s.mapFree s.lam' (s.mapPrefix++[G]) W)
    else if Sandwich k (s.a F) c then
      resolve loc distance F v M N precision q n k (3*q+2) (banks F s.mapFree q)
        s.lam' s.mapPrefix
        (FiniteLabelCrossing.run (fun j=>original (loc j)) (rows distance) (F.image original)
          (after ∅ s.mapPrefix) v s.lam' q n k (copy (3*q)) (copy (3*q+1)) H G T W)
    else .inr (advanceState s G W U)
  | _,_ => .inl (finish s.B s.lam s.P [])

variable [PseudoMetricSpace V]
attribute [local instance] RationalLeaves.metric

lemma step_correct (loc : Fin d → V) (distance : V → Fin d → ℚ)
    (hmetric : ∀ x j,(distance x j:ℝ)=dist x (loc j))
    (F : Finset V) (v M : ℚ) (eta lo hi : ℝ) (N precision q n k : ℕ) (s : State V)
    (h : Certified loc F v eta lo hi q (n+1) k s)
    (hF : F.Nonempty) (hM : 0<M) (hN : 3≤N)
    (hv : (0:ℝ)<(v:ℝ)) (hv1 : (v:ℝ)<1/6) (hlo : 0<lo) (heta : 0≤eta)
    (hhi : hi≤8*N*(M:ℝ)) (hprecision : (1/(2:ℚ)^precision:ℚ)≤eta)
    (hdiam : ∀ i∈F,∀ j,dist i (loc j)≤(M:ℝ)) :
    (step loc distance F v M N precision q n k s).Correct loc F v eta lo hi q n k := by
  obtain ⟨H,T,hT⟩ : ∃ H T,s.T=H::T := by
    cases ht : s.T with
    | nil => have hh:=h.new_tail.1; rw [ht] at hh; simp only [List.length_nil] at hh; omega
    | cons H T => exact ⟨H,T,rfl⟩
  obtain ⟨G,U,hU⟩ : ∃ G U,s.U=G::U := by
    cases ht : s.U with
    | nil => have hh:=h.old_tail.1; rw [ht] at hh; simp only [List.length_nil] at hh; omega
    | cons G U => exact ⟨G,U,rfl⟩
  have hTr := h.new_tail
  rw [hT] at hTr
  obtain ⟨hH,hHr,hTr⟩ := Runs.cons_iff.mp hTr
  have hUr := h.old_tail
  rw [hU] at hUr
  obtain ⟨_,hGr,_⟩ := Runs.cons_iff.mp hUr
  have hG := aligned_phase h hv hv1 hlo G U hU
  have hdis := disjoint_map h.disjoint h.inj h.fixed
  have hp := h.new_prefix
  let W := FiniteLabelContinuation.continuation (fun j=>original (loc j)) (rows distance)
    (F.image original) v s.lam' (q+1) n (after ∅ s.mapPrefix∪G.toFinset)
  have hW : Runs (fun j=>original (loc j)) (F.image original) s.mapFree
      (after ∅ s.mapPrefix∪G.toFinset) v s.lam' (q+1) n W :=
    FiniteLabelContinuation.continuation_spec _ _ (rows_spec loc distance hmetric) _ _ _ _ _ hv hv1 _ _
      (Finset.union_subset hp.after_subset hG.1.opened_subset)
  let c := finalCount (F.image original) (after ∅ s.mapPrefix) G W
  have hfree : (G.toFinset \ F.image original).card≤3 := by
    have hh : G.toFinset⊆F.image original := fun i hi=>hGr i (List.mem_toFinset.mp hi)
    simp only [Finset.sdiff_eq_empty_iff_subset.mpr hh,Finset.card_empty,Nat.zero_le]
  dsimp only [step]
  rw [hT,hU]
  change Outcome.Correct loc F v eta lo hi q n k (if c=k then _ else if Sandwich k (s.a F) c then _ else _)
  split
  next hc =>
    have hh := finish_correct (hp.append_phase hv hv1 ((hlo.trans_le h.low).trans_le h.price) G hG hfree)
      hv hv1 ((hlo.trans_le h.low).trans_le h.price) heta hdis (h.low.trans h.price) h.high
      (T:=W) (n:=n) (by simpa only [after_append,after] using hW)
      (by simpa only [c,finalCount,after_append,after] using hc)
    simpa only [Outcome.Correct,Nat.add_assoc,Nat.add_comm 1 n] using hh
  next hc =>
    split
    next hac =>
      have hcopy : ∀ i∈F.image original,copy (3*q) i∉F.image original∪s.mapFree := by
        intro x hx
        obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
        exact fresh F s.mapFree (3*q) h.before_map i 0
      have hspare : ∀ i∈F.image original,copy (3*q+1) i∉F.image original∪PhaseMergePath.pool (F.image original) s.mapFree (copy (3*q)) := by
        intro x hx
        obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
        exact fresh F _ (3*q+1) (pool_before F s.mapFree (3*q) h.before_map) i 0
      have hdist : ∀ key,∀ i∈F.image original,∀ j,dist (original (loc j)) i=dist (original (loc j)) (copy key i) := by
        intro key x hx j
        obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
        rw [original_dist,copy_dist]
      have hcross := FiniteLabelCrossing.run_spec (fun j=>original (loc j)) (rows distance)
        (rows_spec loc distance hmetric) (F.image original) s.mapFree (after ∅ s.mapPrefix) v s.lam' eta
        q n k (copy (3*q)) (copy (3*q+1)) hv hv1 ((hlo.trans_le h.low).trans_le h.price) heta
        hp.after_subset hdis hp.row hcopy (hdist _) hspare (hdist _) H G T W
        ⟨PhaseMergeSurgery.prefix_exact_eta hH.1 heta,hH.2⟩ hG hHr hGr hTr hW
        (by simpa only [State.a,hT,c,finalCount,after] using hac)
      have hB : Before (3*q+2) (banks F s.mapFree q) := by
        exact pool_before F _ (3*q+1) (pool_before F s.mapFree (3*q) h.before_map)
      have hbdis : Disjoint (F.image original) (banks F s.mapFree q) :=
        CanonicalMergeCrossing.disjoint_pool _ _ _ (CanonicalMergeCrossing.disjoint_pool _ _ _ hdis hcopy) hspare
      exact resolve_correct loc distance hmetric F v M eta lo hi N precision q n k (3*q+2)
        (banks F s.mapFree q) s.lam' s.mapPrefix hF hM hN hB (by omega) hv hv1
        ((hlo.trans_le h.low).trans_le h.price) heta hbdis (h.low.trans h.price) h.high
        (h.high.trans hhi) hprecision hdiam
        (hp.mono_free ((PhaseMergePath.subset_pool ..).trans (PhaseMergePath.subset_pool ..))) _ hcross
    next hac =>
      apply advance_certified h hv hv1 hlo heta G W U hU hW
      have hh:=h.sandwich
      unfold Sandwich at hh hac ⊢
      omega

end MetricKMedianRecovery.CanonicalCoupledMerge

end OAI
