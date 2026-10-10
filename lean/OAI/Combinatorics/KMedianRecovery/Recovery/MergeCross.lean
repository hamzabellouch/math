import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.MergeRefine

namespace OAI

namespace MetricKMedianRecovery.PhaseMergeCompletion
open PhaseSequence PhaseMergeSurgery PhaseHistoryTransfer
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

theorem exists_regular_history (loc : D → X) (F B Q : Finset X) (v lam : ℝ)
    (q n : ℕ) (hQ : Q ⊆ F ∪ B) :
    ∃ T : List (List X), T.length = n ∧ History loc F B v lam 0 q Q T ∧ Regular F T := by
  induction n generalizing q Q with
  | zero => exact ⟨[],rfl,History.nil _ _,by simp [Regular]⟩
  | succ n ih =>
    obtain ⟨H,hH,hreg,hmax⟩ := complete loc F B Q v ((1+v^2)^q) lam 0 le_rfl hQ
    obtain ⟨T,hT,hh,hR⟩ := ih (Q ∪ H.toFinset) (q+1) (Finset.union_subset hQ hH.opened_subset)
    refine ⟨H::T,by simp only [List.length_cons,hT],History.cons ⟨hH,hmax⟩ hh,?_⟩
    intro G hG
    rcases List.mem_cons.mp hG with rfl | hG
    · exact hreg
    · exact hR G hG

theorem prefix_twin (loc : D → X) (F B : Finset X) (v z lam eta : ℝ)
    (i f : X) (_hi : i ∈ F) (hf : f ∈ B) (hdis : Disjoint F B)
    (hd : ∀ j, dist (loc j) i = dist (loc j) f)
    (H : List X) (R : Finset X) (hiR : i ∉ R) (hfR : f ∉ R)
    (hreg : ∀ k ∈ H, k ∈ F) (h : Prefix loc F B v z lam eta (insert i R) H) :
    Prefix loc F B v z lam eta (insert f R) H := by
  have hfF : f ∉ F := fun h => Finset.disjoint_left.mp hdis h hf
  induction H generalizing R with
  | nil => exact Prefix.nil _
  | cons k H ih =>
    cases h with
    | cons hk ht =>
      have hkF : k ∈ F := hreg k (List.mem_cons_self ..)
      have hki : k ≠ i := fun e => hk.1 (e ▸ Finset.mem_insert_self _ _)
      have hkf : k ≠ f := fun e => hfF (e ▸ hkF)
      have hkR : k ∉ R := fun h => hk.1 (Finset.mem_insert_of_mem h)
      have hentry : Entry loc F B (insert f R) v z lam eta k := by
        refine ⟨by simpa only [Finset.mem_insert,not_or] using And.intro hkf hkR,?_⟩
        rcases hk.2 with hkB | ⟨hkF',W,hW,hWF,hop⟩
        · exact (Finset.disjoint_left.mp hdis hkF hkB).elim
        · have hiW : i ∈ W := hW (Finset.mem_insert_self _ _)
          refine Or.inr ⟨hkF',insert f (W.erase i),?_,?_,?_⟩
          · apply Finset.insert_subset_insert
            intro x hx
            exact Finset.mem_erase.mpr ⟨fun e => hiR (e ▸ hx),hW (Finset.mem_insert_of_mem hx)⟩
          · exact Finset.insert_subset (Finset.mem_union_right _ hf) ((Finset.erase_subset _ _).trans hWF)
          · have heq : insert i (W.erase i) = W := Finset.insert_erase hiW
            rw [← heq] at hop
            exact (CoincidentCopy.openable_insert_equal loc F (W.erase i) (1-3*v)
              (1+v^2) v z lam eta i f k hd).mp hop
      have hiR' : i ∉ insert k R := by simpa only [Finset.mem_insert,not_or] using And.intro (Ne.symm hki) hiR
      have hfR' : f ∉ insert k R := by simpa only [Finset.mem_insert,not_or] using And.intro (Ne.symm hkf) hfR
      have htail : Prefix loc F B v z lam eta (insert i (insert k R)) H := by
        simpa only [Finset.insert_comm] using ht
      have hp := ih (insert k R) hiR' hfR' (fun j hj => hreg j (List.mem_cons_of_mem _ hj)) htail
      exact Prefix.cons hentry (by simpa only [Finset.insert_comm] using hp)

lemma absent_after_prefix {loc : D → X} {F B R : Finset X} {v z lam eta : ℝ}
    {i : X} {H : List X} (hiR : i ∉ R)
    (h : Prefix loc F B v z lam eta (insert i R) H) : i ∉ R ∪ H.toFinset := by
  intro hm
  rcases Finset.mem_union.mp hm with hm | hm
  · exact hiR hm
  · exact Finset.disjoint_left.mp h.disjoint (Finset.mem_insert_self _ _) hm

omit [PseudoMetricSpace X] in
lemma free_absent_after {F B R : Finset X} {f : X} {H : List X}
    (hf : f ∈ B) (hdis : Disjoint F B) (hfR : f ∉ R) (hreg : ∀ k ∈ H, k ∈ F) :
    f ∉ R ∪ H.toFinset := by
  intro hm
  rcases Finset.mem_union.mp hm with hm | hm
  · exact hfR hm
  · exact Finset.disjoint_left.mp hdis (hreg f (List.mem_toFinset.mp hm)) hf

theorem history_twin (loc : D → X) (F B : Finset X) (v lam : ℝ)
    (i f : X) (hi : i ∈ F) (hf : f ∈ B) (hdis : Disjoint F B)
    (hd : ∀ j, dist (loc j) i = dist (loc j) f) (ht : 0 ≤ 1-3*v) (hlam : 0 < lam)
    (T : List (List X)) (q : ℕ) (R : Finset X) (hiR : i ∉ R) (hfR : f ∉ R)
    (hreg : Regular F T) (h : History loc F B v lam 0 q (insert i R) T) :
    History loc F B v lam 0 q (insert f R) T ∧
      ∃ U : Finset X, i ∉ U ∧ f ∉ U ∧
        after (insert i R) T = insert i U ∧ after (insert f R) T = insert f U := by
  induction T generalizing q R with
  | nil => exact ⟨History.nil _ _,R,hiR,hfR,rfl,rfl⟩
  | cons H T ih =>
    cases h with
    | cons hH hT =>
      have hHr : ∀ k ∈ H, k ∈ F := hreg H (List.mem_cons_self ..)
      have hp := prefix_twin loc F B v ((1+v^2)^q) lam 0 i f hi hf hdis hd H R hiR hfR hHr hH.1
      have hmax : Maximal loc F (insert i (R ∪ H.toFinset)) v ((1+v^2)^q) lam := by
        simpa only [Finset.insert_union] using hH.2
      have hm := CoincidentCopy.maximal_replace loc F (R ∪ H.toFinset) v ((1+v^2)^q) lam i f hd ht hlam hmax
      have hH' : Valid loc F B (insert f R) v ((1+v^2)^q) lam 0 H :=
        ⟨hp,by simpa only [PhaseSequence.Maximal,Finset.insert_union] using hm⟩
      have hiU := absent_after_prefix hiR hH.1
      have hfU := free_absent_after hf hdis hfR hHr
      have hrT : Regular F T := fun G hG => hreg G (List.mem_cons_of_mem _ hG)
      have hhT : History loc F B v lam 0 (q+1) (insert i (R ∪ H.toFinset)) T := by
        simpa only [Finset.insert_union] using hT
      obtain ⟨hT',U,hiU',hfU',ha,hb⟩ := ih (q+1) (R ∪ H.toFinset) hiU hfU hrT hhT
      refine ⟨History.cons hH' (by simpa only [Finset.insert_union] using hT'),U,hiU',hfU',?_,?_⟩
      · simpa only [after,Finset.insert_union] using ha
      · simpa only [after,Finset.insert_union] using hb

theorem attains_exists (loc : D → X) (F B Q : Finset X) (v lam : ℝ) (q n : ℕ)
    (hQ : Q ⊆ F ∪ B) : ∃ c, Attains loc F B Q v lam q n c := by
  obtain ⟨T,hT,hh,hr⟩ := exists_regular_history loc F B Q v lam q n hQ
  exact ⟨_,T,hT,hh,hr,rfl⟩

lemma attains_zero {loc : D → X} {F B Q : Finset X} {v lam : ℝ} {q c : ℕ}
    (h : Attains loc F B Q v lam q 0 c) : c = (Q ∩ F).card := by
  obtain ⟨T,hT,_,_,hc⟩ := h
  have he : T = [] := List.length_eq_zero_iff.mp hT
  simpa only [he,after] using hc.symm

theorem attains_twin {loc : D → X} {F B Q Q' : Finset X} {v lam : ℝ} {q n c : ℕ}
    (i f : X) (R : Finset X) (hi : i ∈ F) (hf : f ∈ B) (hdis : Disjoint F B)
    (hiR : i ∉ R) (hfR : f ∉ R) (hQ : Q = insert i R) (hQ' : Q' = insert f R)
    (hd : ∀ j, dist (loc j) i = dist (loc j) f) (ht : 0 ≤ 1-3*v) (hlam : 0 < lam)
    (h : Attains loc F B Q v lam q n c) :
    ∃ c', Attains loc F B Q' v lam q n c' ∧ c = c'+1 := by
  obtain ⟨T,hT,hh,hr,hc⟩ := h
  rw [hQ] at hh hc
  obtain ⟨hh',U,hiU,_,ha,hb⟩ := history_twin loc F B v lam i f hi hf hdis hd ht hlam T q R hiR hfR hr hh
  refine ⟨((after Q' T) ∩ F).card,⟨T,hT,by simpa only [hQ'] using hh',hr,rfl⟩,?_⟩
  rw [← hc,ha,hQ',hb,Finset.inter_comm (insert i U),Finset.inter_comm (insert f U)]
  exact CoincidentCopy.paid_count F U i f hi hiU (fun h => Finset.disjoint_left.mp hdis h hf)

end MetricKMedianRecovery.PhaseMergeCompletion
namespace MetricKMedianRecovery.PhaseCountCrossing
open PhaseSequence PhaseMergeRefinement PhaseMergeCompletion PhaseHistoryTransfer
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

def Sandwich (k a b : ℕ) : Prop := (a < k ∧ k < b) ∨ (b < k ∧ k < a)

lemma Sandwich.symm {k a b : ℕ} (h : Sandwich k a b) : Sandwich k b a := Or.symm h

inductive LengthEdit (loc : D → X) (F B : Finset X) : List X → List X → Prop
  | freeAppend (H : List X) (i f : X) (hi : i ∈ F) (hf : f ∈ B)
      (hco : ∀ j, dist (loc j) i = dist (loc j) f) : LengthEdit loc F B H (H++[f])
  | paidDelete (C T : List X) (i : X) (hi : i ∈ F) :
      LengthEdit loc F B (C++i::T) (C++T)

end MetricKMedianRecovery.PhaseCountCrossing

namespace MetricKMedianRecovery.CanonicalMergeCrossing
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion PhaseMergeRefinement PhaseCountCrossing
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

def Runs (loc : D → X) (F B Q : Finset X) (v lam : ℝ) (q n : ℕ)
    (T : List (List X)) : Prop :=
  T.length = n ∧ History loc F B v lam 0 q Q T ∧ Regular F T

def paid (F Q : Finset X) (H : List X) : ℕ := ((Q ∪ H.toFinset) ∩ F).card

def finalCount (F Q : Finset X) (H : List X) (T : List (List X)) : ℕ :=
  ((after (Q ∪ H.toFinset) T) ∩ F).card

lemma Runs.attains {loc : D → X} {F B Q : Finset X} {v lam : ℝ} {q n : ℕ}
    {T : List (List X)} (h : Runs loc F B Q v lam q n T) :
    Attains loc F B Q v lam q n ((after Q T) ∩ F).card := ⟨T,h.1,h.2.1,h.2.2,rfl⟩

def continuation {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v lam : ℚ) (q n : ℕ) (Q : Finset (Fin m)) : List (List (Fin m)) :=
  (RationalPhase.historyRun distance F v lam n ⟨Q,(1+v^2)^q,Vector.replicate d 0⟩).2

lemma continuation_spec {m d : ℕ} [PseudoMetricSpace (Fin m)]
    (loc : Fin d → Fin m) (distance : Fin m → Fin d → ℚ)
    (hd : ∀ f j,(distance f j:ℝ)=dist f (loc j))
    (F B Q : Finset (Fin m)) (v lam : ℚ)
    (hv : (0:ℝ)<(v:ℝ)) (hv1 : (v:ℝ)<1/6) (q n : ℕ) (hQ : Q⊆F∪B) :
    Runs loc F B Q v lam q n (continuation distance F v lam q n Q) := by
  obtain ⟨hn,hh,hr,_⟩ := RationalPhase.historyRun_spec loc distance hd F B v lam hv hv1 n q
    ⟨Q,(1+v^2)^q,Vector.replicate d 0⟩ rfl hQ
  exact ⟨hn,hh,hr⟩

inductive Result (X : Type*) where
  | success (H : List X) (T : List (List X))
  | common (H : List X) (T U : List (List X))
  | sensitive (H G : List X) (T U : List (List X))

def Result.Correct (loc : D → X) (F B Q : Finset X) (v lam eta : ℝ) (q n k : ℕ) :
    Result X → Prop
  | .success H T => Good loc F B Q v ((1+v^2)^q) lam eta H ∧
      Runs loc F B (Q ∪ H.toFinset) v lam (q+1) n T ∧ finalCount F Q H T = k
  | .common H T U => Good loc F B Q v ((1+v^2)^q) lam eta H ∧
      Runs loc F B (Q ∪ H.toFinset) v lam (q+1) n T ∧
      Runs loc F B (Q ∪ H.toFinset) v lam (q+1) n U ∧
      Sandwich k (finalCount F Q H T) (finalCount F Q H U)
  | .sensitive H G T U => Good loc F B Q v ((1+v^2)^q) lam eta H ∧
      Good loc F B Q v ((1+v^2)^q) lam eta G ∧ LengthEdit loc F B H G ∧
      Runs loc F B (Q ∪ H.toFinset) v lam (q+1) n T ∧
      Runs loc F B (Q ∪ G.toFinset) v lam (q+1) n U ∧
      Sandwich k (finalCount F Q H T) (finalCount F Q G U)

lemma twin_replay (loc : D → X) (F B Q : Finset X) (v lam eta : ℝ)
    (q n : ℕ) (H G : List X) (T : List (List X))
    (hQ : Q ⊆ F ∪ B) (hdis : Disjoint F B) (ht : 0 ≤ 1-3*v) (hlam : 0 < lam)
    (hG : Good loc F B Q v ((1+v^2)^q) lam eta G)
    (hco : Coincident loc F Q H G)
    (hT : Runs loc F B (Q ∪ H.toFinset) v lam (q+1) n T) :
    Runs loc F B (Q ∪ G.toFinset) v lam (q+1) n T ∧
      finalCount F Q H T = finalCount F Q G T + 1 := by
  obtain ⟨i,f,R,hi,hfF,hiR,hfR,hHq,hGq,hd⟩ := hco
  have hfQ : f ∈ Q ∪ G.toFinset := hGq ▸ Finset.mem_insert_self f R
  have hf : f ∈ B := (Finset.mem_union.mp
    ((Finset.union_subset hQ hG.1.1.opened_subset) hfQ)).resolve_left hfF
  have hh : History loc F B v lam 0 (q+1) (insert i R) T := hHq ▸ hT.2.1
  obtain ⟨hh',U,hiU,_,ha,hb⟩ := history_twin loc F B v lam i f hi hf hdis hd ht hlam
    T (q+1) R hiR hfR hT.2.2 hh
  refine ⟨⟨hT.1,hGq.symm ▸ hh',hT.2.2⟩,?_⟩
  simp only [finalCount,hHq,hGq,ha,hb,Finset.inter_comm (insert i U),Finset.inter_comm (insert f U)]
  exact CoincidentCopy.paid_count F U i f hi hiU hfF

omit [Fintype D] in
lemma coincident_paid {loc : D → X} {F Q : Finset X} {H G : List X}
    (hco : Coincident loc F Q H G) : paid F Q H = paid F Q G + 1 := by
  obtain ⟨i,f,R,hi,hfF,hiR,_,hHq,hGq,_⟩ := hco
  simp only [paid,hHq,hGq,Finset.inter_comm (insert i R),Finset.inter_comm (insert f R)]
  exact CoincidentCopy.paid_count F R i f hi hiR hfF

lemma coincident_length {loc : D → X} {F B Q : Finset X} {v z lam eta : ℝ} {H G : List X}
    (hH : Valid loc F B Q v z lam eta H) (hG : Valid loc F B Q v z lam eta G)
    (hco : Coincident loc F Q H G) : H.length=G.length := by
  obtain ⟨i,f,R,_,_,hiR,hfR,hHq,hGq,_⟩ := hco
  have hh := congrArg Finset.card hHq
  have hg := congrArg Finset.card hGq
  rw [Finset.card_union_of_disjoint hH.1.disjoint,List.toFinset_card_of_nodup hH.1.nodup,
    Finset.card_insert_of_notMem hiR] at hh
  rw [Finset.card_union_of_disjoint hG.1.disjoint,List.toFinset_card_of_nodup hG.1.nodup,
    Finset.card_insert_of_notMem hfR] at hg
  omega

def forward (F Q : Finset X) (H G : List X) : Bool :=
  if paid F Q H = paid F Q G then decide (H.length < G.length)
  else decide (paid F Q G < paid F Q H)

omit [PseudoMetricSpace X] in
lemma forward_reverse {F Q : Finset X} {H G : List X}
    (h : forward F Q H G = true) : forward F Q G H = false := by
  unfold forward at *
  split at h
  · rename_i he
    rw [ite_eq_left he.symm]
    simp only [decide_eq_true_eq] at h
    exact decide_eq_false (by omega)
  · rename_i he
    rw [ite_eq_right (Ne.symm he)]
    simp only [decide_eq_true_eq] at h
    exact decide_eq_false (by omega)

omit [PseudoMetricSpace X] in
lemma freeAppend_paid (F Q : Finset X) (H : List X) (f : X) (hf : f ∉ F) :
    paid F Q (H++[f]) = paid F Q H := by
  unfold paid
  congr 1
  ext x
  simp only [List.toFinset_append,List.toFinset_cons,List.toFinset_nil,Finset.mem_insert,Finset.notMem_empty,or_false,
    Finset.mem_inter,Finset.mem_union]
  constructor
  · rintro ⟨h,hx⟩
    rcases h with h|h|rfl
    · exact ⟨Or.inl h,hx⟩
    · exact ⟨Or.inr h,hx⟩
    · exact (hf hx).elim
  · rintro ⟨h,hx⟩
    exact ⟨h.imp_right Or.inl,hx⟩

lemma paidDelete_paid {loc : D → X} {F B Q : Finset X} {v z lam eta : ℝ}
    (C T : List X) (i : X) (hi : i ∈ F)
    (hH : Valid loc F B Q v z lam eta (C++i::T)) :
    paid F Q (C++i::T) = paid F Q (C++T) + 1 := by
  have hnot := entry_fresh hH.1
  have hset : Q ∪ (C++i::T).toFinset = insert i (Q ∪ (C++T).toFinset) := by
    simp only [List.toFinset_append,List.toFinset_cons,Finset.union_insert]
  unfold paid
  rw [hset,Finset.insert_inter_of_mem hi,Finset.card_insert_of_notMem]
  exact fun hh => hnot (Finset.mem_of_mem_inter_left hh)

lemma edit_forward {loc : D → X} {F B Q : Finset X} {v z lam eta : ℝ}
    {H G : List X} (hdis : Disjoint F B)
    (hH : Valid loc F B Q v z lam eta H) (he : Edit loc F B Q H G) :
    forward F Q H G = true := by
  cases he with
  | freeAppend H i f hi hf hd =>
    have hfF : f∉F := fun hh => Finset.disjoint_left.mp hdis hh hf
    rw [forward,freeAppend_paid F Q H f hfF,ite_eq_left rfl]
    simp only [List.length_append,List.length_singleton,decide_eq_true_eq]
    omega
  | paidDelete C T i hi =>
    have hh := paidDelete_paid C T i hi hH
    rw [forward,ite_eq_right (by omega)]
    exact decide_eq_true (by omega)
  | coincident hc =>
    have hh := coincident_paid hc
    rw [forward,ite_eq_right (by omega)]
    exact decide_eq_true (by omega)

def directed (F Q : Finset X) (k : ℕ) (H G : List X) (T U : List (List X)) : Result X :=
  if H.length=G.length then
    if finalCount F Q G T=k then .success G T else .common G T U
  else .sensitive H G T U

def edge (F Q : Finset X) (k : ℕ) (H G : List X) (T U : List (List X)) : Result X :=
  if forward F Q H G then directed F Q k H G T U else directed F Q k G H U T

lemma directed_spec (loc : D → X) (F B Q : Finset X) (v lam eta : ℝ)
    (q n k : ℕ) (H G : List X) (T U : List (List X))
    (hQ : Q ⊆ F ∪ B) (hdis : Disjoint F B) (ht : 0 ≤ 1-3*v) (hlam : 0 < lam)
    (hH : Good loc F B Q v ((1+v^2)^q) lam eta H)
    (hG : Good loc F B Q v ((1+v^2)^q) lam eta G)
    (he : Edit loc F B Q H G)
    (hs : Sandwich k (finalCount F Q H T) (finalCount F Q G U))
    (hT : Runs loc F B (Q ∪ H.toFinset) v lam (q+1) n T)
    (hU : Runs loc F B (Q ∪ G.toFinset) v lam (q+1) n U) :
    (directed F Q k H G T U).Correct loc F B Q v lam eta q n k := by
  cases he with
  | freeAppend H i f hi hf hd =>
    have hne : H.length≠(H++[f]).length := by simp only [List.length_append,List.length_singleton]; omega
    rw [directed,ite_eq_right hne]
    exact ⟨hH,hG,.freeAppend H i f hi hf hd,hT,hU,hs⟩
  | paidDelete C T' i hi =>
    have hne : (C++i::T').length≠(C++T').length := by
      simp only [List.length_append,List.length_cons]; omega
    rw [directed,ite_eq_right hne]
    exact ⟨hH,hG,.paidDelete C T' i hi,hT,hU,hs⟩
  | coincident hc =>
    have hlen := coincident_length hH.1 hG.1 hc
    have hh := twin_replay loc F B Q v lam eta q n H G T hQ hdis ht hlam hG hc hT
    rw [directed,ite_eq_left hlen]
    split
    · rename_i hk
      exact ⟨hG,hh.1,hk⟩
    · rename_i hk
      refine ⟨hG,hh.1,hU,?_⟩
      obtain heq := hh.2
      rcases hs with hs|hs <;> unfold Sandwich <;> omega

lemma edge_spec (loc : D → X) (F B Q : Finset X) (v lam eta : ℝ)
    (q n k : ℕ) (H G : List X) (T U : List (List X))
    (hQ : Q ⊆ F ∪ B) (hdis : Disjoint F B) (ht : 0 ≤ 1-3*v) (hlam : 0 < lam)
    (hH : Good loc F B Q v ((1+v^2)^q) lam eta H)
    (hG : Good loc F B Q v ((1+v^2)^q) lam eta G)
    (he : Adjacent loc F B Q H G)
    (hs : Sandwich k (finalCount F Q H T) (finalCount F Q G U))
    (hT : Runs loc F B (Q ∪ H.toFinset) v lam (q+1) n T)
    (hU : Runs loc F B (Q ∪ G.toFinset) v lam (q+1) n U) :
    (edge F Q k H G T U).Correct loc F B Q v lam eta q n k := by
  rcases he with he|he
  · have hh := edit_forward hdis hH.1 he
    rw [edge,hh]
    exact directed_spec loc F B Q v lam eta q n k H G T U hQ hdis ht hlam hH hG he hs hT hU
  · have hh := forward_reverse (edit_forward hdis hG.1 he)
    rw [edge,hh]
    exact directed_spec loc F B Q v lam eta q n k G H U T hQ hdis ht hlam hG hH he hs.symm hU hT

instance (k a b : ℕ) : Decidable (Sandwich k a b) := inferInstanceAs (Decidable ((_ ∧ _) ∨ (_ ∧ _)))

def scan (F Q : Finset X) (k : ℕ) (complete : Finset X → List (List X))
    (U : List (List X)) : List X → List (List X) → List (List X) → Result X
  | H,T,[] => .common H T U
  | H,T,J::S =>
    let V := complete (Q ∪ J.toFinset)
    if finalCount F Q J V = k then .success J V
    else if Sandwich k (finalCount F Q H T) (finalCount F Q J V) then edge F Q k H J T V
    else scan F Q k complete U J V S

lemma scan_spec (loc : D → X) (F B Q : Finset X) (v lam eta : ℝ)
    (q n k : ℕ) (complete : Finset X → List (List X))
    (hcomplete : ∀ R, R⊆F∪B → Runs loc F B R v lam (q+1) n (complete R))
    (hQ : Q ⊆ F ∪ B) (hdis : Disjoint F B) (ht : 0 ≤ 1-3*v) (hlam : 0 < lam)
    {H G : List X} {S : List (List X)}
    (hp : CanonicalMergeRefinement.EPath loc F B Q v ((1+v^2)^q) lam eta H S G)
    (T U : List (List X))
    (hs : Sandwich k (finalCount F Q H T) (finalCount F Q G U))
    (hT : Runs loc F B (Q ∪ H.toFinset) v lam (q+1) n T)
    (hU : Runs loc F B (Q ∪ G.toFinset) v lam (q+1) n U) :
    (scan F Q k complete U H T S).Correct loc F B Q v lam eta q n k := by
  induction hp generalizing T with
  | nil hH => exact ⟨hH,hT,hU,hs⟩
  | @cons H J S G hH he htail ih =>
    have hJ := htail.toChain.first_good
    have hV := hcomplete (Q ∪ J.toFinset) (Finset.union_subset hQ hJ.1.1.opened_subset)
    dsimp only [scan]
    split
    · rename_i hk
      exact ⟨hJ,hV,hk⟩
    · rename_i hk
      split
      · rename_i hs'
        exact edge_spec loc F B Q v lam eta q n k H J T _ hQ hdis ht hlam hH hJ he hs' hT hV
      · rename_i hs'
        have hs'' : Sandwich k (finalCount F Q J (complete (Q ∪ J.toFinset))) (finalCount F Q G U) := by
          unfold Sandwich at *
          omega
        exact ih _ hs'' hV hU

lemma Runs.mono_free {loc : D → X} {F B B' Q : Finset X} {v lam : ℝ} {q n : ℕ}
    {T : List (List X)} (h : Runs loc F B Q v lam q n T) (hB : B⊆B') :
    Runs loc F B' Q v lam q n T := by
  refine ⟨h.1,?_,h.2.2⟩
  have hh := h.2.1
  clear h
  induction hh with
  | nil => exact .nil _ _
  | cons hhead htail ih =>
    exact .cons ⟨PhaseMergeSurgery.prefix_free_mono hhead.1 hB,hhead.2⟩ ih

omit [Fintype D] [PseudoMetricSpace X] in
lemma disjoint_pool (F B : Finset X) (copy : X → X) (hdis : Disjoint F B)
    (hc : ∀ i∈F,copy i∉F∪B) : Disjoint F (PhaseMergePath.pool F B copy) := by
  rw [Finset.disjoint_left]
  intro x hx hxpool
  rcases Finset.mem_union.mp hxpool with hxB|hxc
  · exact Finset.disjoint_left.mp hdis hx hxB
  · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hxc
    exact hc i hi (Finset.mem_union_left _ hx)

def regularCross {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F Q : Finset (Fin m))
    (v lam : ℚ) (q n k : ℕ) (copy spare : Fin m → Fin m) (H G : List (Fin m))
    (T U : List (List (Fin m))) : Result (Fin m) :=
  let complete := RationalPhase.completion distance F v ((1+v^2)^q) lam
  let S := CanonicalMergeRefinement.regularChain F (List.ofFn id) complete Q copy spare H G
  scan F Q k (continuation distance F v lam (q+1) n) U H T S

 theorem regularCross_spec {m d : ℕ} [PseudoMetricSpace (Fin m)]
    (loc : Fin d → Fin m) (distance : Fin m → Fin d → ℚ)
    (hmetric : ∀ f j,(distance f j:ℝ)=dist f (loc j)) (F B Q : Finset (Fin m))
    (v lam : ℚ) (eta : ℝ) (q n k : ℕ) (copy spare : Fin m → Fin m)
    (hv : (0:ℝ)<(v:ℝ)) (hvsmall : (v:ℝ)<1/6) (hlam : (0:ℝ)<(lam:ℝ)) (heta : 0≤eta)
    (hQ : Q⊆F∪B) (hdis : Disjoint F B)
    (hrow : ∀ i∈F,bidRow loc (1-3*(v:ℝ)) ((1+(v:ℝ)^2)^q) Q i ≤ (lam:ℝ))
    (hc : ∀ i∈F,copy i∉F∪B) (hd : ∀ i∈F,∀ j,dist (loc j) i=dist (loc j) (copy i))
    (hs : ∀ i∈F,spare i∉F∪PhaseMergePath.pool F B copy)
    (he : ∀ i∈F,∀ j,dist (loc j) i=dist (loc j) (spare i))
    (H G : List (Fin m)) (T U : List (List (Fin m)))
    (hH : Valid loc F B Q v ((1+(v:ℝ)^2)^q) lam eta H)
    (hG : Valid loc F B Q v ((1+(v:ℝ)^2)^q) lam eta G)
    (hHr : ∀ i∈H,i∈F) (hGr : ∀ i∈G,i∈F)
    (hT : Runs loc F B (Q∪H.toFinset) v lam (q+1) n T)
    (hU : Runs loc F B (Q∪G.toFinset) v lam (q+1) n U)
    (hbr : Sandwich k (finalCount F Q H T) (finalCount F Q G U)) :
    (regularCross distance F Q v lam q n k copy spare H G T U).Correct loc F
      (PhaseMergePath.pool F (PhaseMergePath.pool F B copy) spare) Q v lam eta q n k := by
  let B' := PhaseMergePath.pool F (PhaseMergePath.pool F B copy) spare
  have hB : B⊆B' := (PhaseMergePath.subset_pool F B copy).trans (PhaseMergePath.subset_pool ..)
  let complete := RationalPhase.completion distance F v ((1+v^2)^q) lam
  have hz : (((1+v^2)^q:ℚ):ℝ)=(1+(v:ℝ)^2)^q := by push_cast; rfl
  have hcomp : CanonicalMergePath.CorrectCompletion loc F v ((1+(v:ℝ)^2)^q) lam complete := by
    have hh := CanonicalMergePath.rational_correct loc distance hmetric F v ((1+v^2)^q) lam
      hv hvsmall (by rw [hz]; positivity)
    simpa only [hz] using hh
  obtain ⟨_,hp⟩ := CanonicalMergeRefinement.regularChain_spec loc F B Q (List.ofFn id) copy spare
    v ((1+(v:ℝ)^2)^q) lam eta complete hcomp hv hvsmall (by positivity) hlam heta
    (fun i _ => List.mem_ofFn.mpr ⟨i,rfl⟩) hQ hdis hrow hc hd hs he H G hH hG hHr hGr
  apply scan_spec loc F B' Q v lam eta q n k _ _
    (hQ.trans (Finset.union_subset_union_right hB))
    (disjoint_pool F _ spare (disjoint_pool F B copy hdis hc) hs)
    (by linarith) hlam hp T U hbr (hT.mono_free hB) (hU.mono_free hB)
  intro R hR
  exact continuation_spec loc distance hmetric F B' R v lam hv hvsmall (q+1) n hR

end MetricKMedianRecovery.CanonicalMergeCrossing

end OAI
