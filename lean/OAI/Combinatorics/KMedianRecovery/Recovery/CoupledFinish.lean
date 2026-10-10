import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.LeafOrder

namespace OAI

namespace MetricKMedianRecovery.CanonicalCoupledMerge
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion PhaseMergeRefinement PhaseCountCrossing
  CanonicalMergeCrossing RationalLeaves PhaseMergeInvariant PhaseCoupledMerge
variable {V : Type*} [PseudoMetricSpace V] [DecidableEq V] {d : ℕ}
attribute [local instance] RationalLeaves.metric

def finish (B : Finset (Label V)) (lam : ℚ) (P T : List (List (Label V))) : Output V :=
  ⟨B,lam,P++T⟩

lemma finish_correct {loc : Fin d → V} {F : Finset V} {B : Finset (Label V)}
    {v eta lo hi : ℝ} {lam : ℚ} {q n k : ℕ} {P T : List (List (Label V))}
    (hp : PrefixData (fun j=>original (loc j)) (F.image original) B v lam eta q P)
    (hv : 0<v) (hv1 : v<1/6) (hlam : (0:ℝ)<lam) (heta : 0≤eta)
    (hd : Disjoint (F.image original) B) (hl : lo≤(lam:ℝ)) (hu : (lam:ℝ)≤hi)
    (hT : Runs (fun j=>original (loc j)) (F.image original) B (after ∅ P) v lam q n T)
    (hc : ((after (after ∅ P) T)∩F.image original).card=k) :
    (finish B lam P T).Correct loc F v eta lo hi (q+n) k := by
  refine ⟨hd,hl,hu,?_,?_⟩
  · simpa only [hT.1,finish] using hp.append_exact hv hv1 hlam heta T hT.2.1 hT.2.2
  · simpa only [finish,after_append] using hc

def sameState (B : Finset (Label V)) (lam : ℚ) (P T U : List (List (Label V))) : State V :=
  ⟨B,P,.identity,lam,lam,T,U⟩

lemma same_certified {loc : Fin d → V} {F : Finset V} {B : Finset (Label V)}
    {v eta lo hi : ℝ} {lam : ℚ} {q n k : ℕ} {P T U : List (List (Label V))}
    (hB : Before (3*q) B) (heta : 0≤eta) (hd : Disjoint (F.image original) B)
    (hl : lo≤(lam:ℝ)) (hu : (lam:ℝ)≤hi)
    (hp : PrefixData (fun j=>original (loc j)) (F.image original) B v lam eta q P)
    (hT : Runs (fun j=>original (loc j)) (F.image original) B (after ∅ P) v lam q n T)
    (hU : Runs (fun j=>original (loc j)) (F.image original) B (after ∅ P) v lam q n U)
    (hs : Sandwich k ((after (after ∅ P) T)∩F.image original).card
      ((after (after ∅ P) U)∩F.image original).card) :
    Certified loc F v eta lo hi q n k (sameState B lam P T U) := by
  refine {
    before := hB
    before_map := ?_
    disjoint := hd
    low := hl
    high := hu
    price := le_rfl
    eps_nonneg := by norm_num [sameState,Correction.error]
    error := ?_
    inj := Function.injective_id
    fixed := fun _ _=>rfl
    shrink := fun _ _ _=>le_rfl
    loss := ?_
    old_prefix := hp
    new_prefix := ?_
    sandwich := ?_
    new_tail := ?_
    old_tail := hU }
  · simpa only [sameState,State.mapFree,Correction.apply,Finset.image_id] using hB
  · change (lam:ℝ)-lam+(d:ℝ)*((1-3*v)*(0:ℚ))≤(d:ℝ)*eta
    simpa only [Rat.cast_zero,sub_self,mul_zero,add_zero] using mul_nonneg (Nat.cast_nonneg d) heta
  · intro j x _
    change dist _ x≤dist _ x+(0:ℚ)
    simp
  · simpa only [sameState,State.mapPrefix,State.mapFree,Correction.apply,Finset.image_id,List.map_id_fun,List.map_id] using hp
  · simpa only [sameState,State.a,State.b,State.mapPrefix,Correction.apply,List.map_id_fun,List.map_id] using hs
  · simpa only [sameState,State.mapPrefix,State.mapFree,Correction.apply,Finset.image_id,List.map_id_fun,List.map_id] using hT

end MetricKMedianRecovery.CanonicalCoupledMerge

namespace MetricKMedianRecovery.CanonicalMergeCrossing
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]
lemma Runs.cons_iff {loc : D → X} {F B Q : Finset X} {v lam : ℝ} {q n : ℕ}
    {H : List X} {T : List (List X)} :
    Runs loc F B Q v lam q (n+1) (H::T) ↔
      Valid loc F B Q v ((1+v^2)^q) lam 0 H ∧ (∀ i∈H,i∈F) ∧
      Runs loc F B (Q∪H.toFinset) v lam (q+1) n T := by
  constructor
  · rintro ⟨hlen,hh,hr⟩
    cases hh with
    | cons hH hT =>
      exact ⟨hH,fun i hi=>hr H (List.mem_cons_self ..) i hi,
        by simpa only [List.length_cons,Nat.add_right_cancel_iff] using hlen,
        hT,fun G hG=>hr G (List.mem_cons_of_mem _ hG)⟩
  · rintro ⟨hH,hHr,hT⟩
    refine ⟨by simp only [List.length_cons,hT.1],History.cons hH hT.2.1,?_⟩
    intro G hG
    rcases List.mem_cons.mp hG with rfl|hG
    · exact hHr
    · exact hT.2.2 G hG
end MetricKMedianRecovery.CanonicalMergeCrossing

namespace MetricKMedianRecovery.CanonicalCoupledMerge
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion PhaseMergeRefinement PhaseCountCrossing
  CanonicalMergeCrossing RationalLeaves PhaseMergeInvariant PhaseCoupledMerge
variable {V : Type*} [PseudoMetricSpace V] [DecidableEq V] {d : ℕ}
attribute [local instance] RationalLeaves.metric

lemma aligned_phase {loc : Fin d → V} {F : Finset V} {v eta lo hi : ℝ}
    {q n k : ℕ} {s : State V} (h : Certified loc F v eta lo hi q (n+1) k s)
    (hv : 0<v) (hv1 : v<1/6) (hlo : 0<lo) (G : List (Label V)) (U : List (List (Label V)))
    (hU : s.U=G::U) :
    Valid (fun j=>original (loc j)) (F.image original) s.mapFree (after ∅ s.mapPrefix)
      v ((1+v^2)^q) s.lam' eta G := by
  have hh := h.old_tail
  rw [hU] at hh
  obtain ⟨hG,hGr,_⟩ := Runs.cons_iff.mp hh
  have halign := PhaseParameterAlignment.align (fun j=>original (loc j)) (F.image original)
    s.B (after ∅ s.P) G s.correction.apply v s.lam s.lam' eta s.correction.error q n k (s.a F) (s.b F)
    hv hv1 (hlo.trans_le h.low) h.eps_nonneg h.price (by simpa only [Fintype.card_fin] using h.error)
    h.inj h.fixed h.old_prefix.after_subset h.shrink h.loss h.old_prefix.row hG hGr h.sandwich
  have hafter : (after ∅ s.P).image s.correction.apply=after ∅ s.mapPrefix := by
    simpa only [Finset.image_empty,State.mapPrefix] using (PhaseHistoryTransfer.after_map ∅ s.P s.correction.apply).symm
  simpa only [State.mapFree,hafter] using halign.1

def advanceState (s : State V) (G : List (Label V)) (T U : List (List (Label V))) : State V :=
  { s with P := s.P++[G],T := T,U := U }

lemma advance_certified {loc : Fin d → V} {F : Finset V} {v eta lo hi : ℝ}
    {q n k : ℕ} {s : State V} (h : Certified loc F v eta lo hi q (n+1) k s)
    (hv : 0<v) (hv1 : v<1/6) (hlo : 0<lo) (heta : 0≤eta)
    (G : List (Label V)) (T U : List (List (Label V))) (hU : s.U=G::U)
    (hT : Runs (fun j=>original (loc j)) (F.image original) s.mapFree
      (after ∅ s.mapPrefix∪G.toFinset) v s.lam' (q+1) n T)
    (hs : Sandwich k (finalCount (F.image original) (after ∅ s.mapPrefix) G T) (s.b F)) :
    Certified loc F v eta lo hi (q+1) n k (advanceState s G T U) := by
  have hh := h.old_tail
  rw [hU] at hh
  obtain ⟨hG,hGr,hUr⟩ := Runs.cons_iff.mp hh
  have hG' := aligned_phase h hv hv1 hlo G U hU
  have hfree : (G.toFinset \ F.image original).card≤3 := by
    have hh : G.toFinset⊆F.image original := fun i hi=>hGr i (List.mem_toFinset.mp hi)
    simp only [Finset.sdiff_eq_empty_iff_subset.mpr hh,Finset.card_empty,Nat.zero_le]
  have he : (s.P++[G]).map (List.map s.correction.apply)=s.mapPrefix++[G] := by
    simp only [List.map_append,List.map_cons,List.map_nil,
      PhaseParameterAlignment.regular_map_eq (F.image original) G s.correction.apply h.fixed hGr,State.mapPrefix]
  refine {
    before := h.before.mono (by omega)
    before_map := h.before_map.mono (by omega)
    disjoint := h.disjoint
    low := h.low
    high := h.high
    price := h.price
    eps_nonneg := h.eps_nonneg
    error := h.error
    inj := h.inj
    fixed := h.fixed
    shrink := h.shrink
    loss := h.loss
    old_prefix := h.old_prefix.append_phase hv hv1 (hlo.trans_le h.low) G
      ⟨PhaseMergeSurgery.prefix_exact_eta hG.1 heta,hG.2⟩ hfree
    new_prefix := ?_
    sandwich := ?_
    new_tail := ?_
    old_tail := ?_ }
  · change PrefixData _ _ s.mapFree _ _ _ _ ((s.P++[G]).map (List.map s.correction.apply))
    rw [he]
    exact h.new_prefix.append_phase hv hv1 ((hlo.trans_le h.low).trans_le h.price) G hG' hfree
  · change Sandwich k ((after (after ∅ ((s.P++[G]).map (List.map s.correction.apply))) T)∩F.image original).card
      ((after (after ∅ (s.P++[G])) U)∩F.image original).card
    simpa only [finalCount,List.toFinset_nil,Finset.union_empty,he,after_append,after,State.b,hU] using hs
  · change Runs _ _ s.mapFree (after ∅ ((s.P++[G]).map (List.map s.correction.apply))) _ _ _ _ T
    simpa only [he,after_append,after,advanceState] using hT
  · change Runs _ _ s.B (after ∅ (s.P++[G])) _ _ _ _ U
    simpa only [after_append,after,advanceState] using hUr

end MetricKMedianRecovery.CanonicalCoupledMerge

end OAI
