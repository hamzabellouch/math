import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.EntryFreeMono
import OAI.Combinatorics.KMedianRecovery.Sampling.PrefixFreeMono
import OAI.Combinatorics.KMedianRecovery.Strictness.ClippedMap

namespace OAI

namespace MetricKMedianRecovery.PhaseMergeInvariant
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion
universe uD uX uY
variable {D : Type uD} {X : Type uX} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

structure PrefixData (loc : D → X) (F B : Finset X) (v lam eta : ℝ)
    (q : ℕ) (P : List (List X)) : Prop where
  length_eq : P.length = q
  history : History loc F B v lam eta 0 ∅ P
  free_bound : ∀ H ∈ P, (H.toFinset \ F).card ≤ 3
  row : ∀ i ∈ F, bidRow loc (1-3*v) ((1+v^2)^q) (after ∅ P) i ≤ lam

omit [Fintype D] [PseudoMetricSpace X] in
lemma after_append (Q : Finset X) (P T : List (List X)) :
    after Q (P++T) = after (after Q P) T := by
  induction P generalizing Q with
  | nil => rfl
  | cons H P ih => exact ih _

lemma history_exact_eta {loc : D → X} {F B Q : Finset X} {v lam eta : ℝ}
    {q : ℕ} {P : List (List X)} (h : History loc F B v lam 0 q Q P) (heta : 0 ≤ eta) :
    History loc F B v lam eta q Q P := by
  induction h with
  | nil => exact History.nil _ _
  | cons hhead htail ih =>
    exact History.cons ⟨PhaseMergeSurgery.prefix_exact_eta hhead.1 heta,hhead.2⟩ ih

lemma PrefixData.after_subset {loc : D → X} {F B : Finset X} {v lam eta : ℝ}
    {q : ℕ} {P : List (List X)} (h : PrefixData loc F B v lam eta q P) :
    after ∅ P ⊆ F ∪ B := h.history.after_subset (Finset.empty_subset _)

lemma PrefixData.mono_free {loc : D → X} {F B B' : Finset X} {v lam eta : ℝ}
    {q : ℕ} {P : List (List X)} (h : PrefixData loc F B v lam eta q P) (hB : B ⊆ B') :
    PrefixData loc F B' v lam eta q P :=
  ⟨h.length_eq,CommonPrefixTransfer.history_free_mono loc F B B' ∅ v lam eta 0 P hB h.history,
    h.free_bound,h.row⟩

lemma PrefixData.append_phase {loc : D → X} {F B : Finset X} {v lam eta : ℝ}
    {q : ℕ} {P : List (List X)} (h : PrefixData loc F B v lam eta q P)
    (hv : 0 < v) (hvsmall : v < 1/6) (hlam : 0 < lam)
    (H : List X) (hh : Valid loc F B (after ∅ P) v ((1+v^2)^q) lam eta H)
    (hfree : (H.toFinset \ F).card ≤ 3) :
    PrefixData loc F B v lam eta (q+1) (P++[H]) := by
  refine ⟨by simp only [List.length_append,List.length_singleton,h.length_eq],?_,?_,?_⟩
  · apply CommonPrefixTransfer.history_append loc F B ∅ v lam eta 0 P [H] h.history
    simpa only [Nat.zero_add,h.length_eq] using History.cons hh (History.nil _ _)
  · intro G hG
    rcases List.mem_append.mp hG with hG | hG
    · exact h.free_bound G hG
    · simpa only [List.mem_singleton.mp hG] using hfree
  · simpa only [after_append,after] using
      advance_rows loc F B (after ∅ P) v lam eta q H hv hvsmall hlam h.row hh

lemma PrefixData.append_exact {loc : D → X} {F B : Finset X} {v lam eta : ℝ}
    {q : ℕ} {P : List (List X)} (h : PrefixData loc F B v lam eta q P)
    (hv : 0 < v) (hvsmall : v < 1/6) (hlam : 0 < lam) (heta : 0 ≤ eta)
    (T : List (List X)) (hh : History loc F B v lam 0 q (after ∅ P) T)
    (hreg : Regular F T) : PrefixData loc F B v lam eta (q+T.length) (P++T) := by
  refine ⟨by simp only [List.length_append,h.length_eq],?_,?_,?_⟩
  · apply CommonPrefixTransfer.history_append loc F B ∅ v lam eta 0 P T h.history
    simpa only [Nat.zero_add,h.length_eq] using history_exact_eta hh heta
  · intro H hH
    rcases List.mem_append.mp hH with hH | hH
    · exact h.free_bound H hH
    · have hs : H.toFinset ⊆ F := fun i hi => hreg H hH i (List.mem_toFinset.mp hi)
      simp only [Finset.sdiff_eq_empty_iff_subset.mpr hs,Finset.card_empty,Nat.zero_le]
  · rw [after_append]
    exact CommonPrefixTransfer.history_rows loc F B (after ∅ P) v lam 0 q T
      hv hvsmall hlam h.row hh

lemma PrefixData.map {Y : Type uY} [PseudoMetricSpace Y] [DecidableEq Y]
    {loc : D → X} {F B : Finset X} {v lam eta : ℝ} {q : ℕ} {P : List (List X)}
    (h : PrefixData loc F B v lam eta q P) (e : X ↪ Y)
    (he : ∀ x y, dist (e x) (e y) = dist x y) :
    PrefixData (fun j => e (loc j)) (F.image e) (B.image e) v lam eta q
      (P.map (List.map e)) := by
  refine ⟨by simpa only [List.length_map] using h.length_eq,?_,?_,?_⟩
  · simpa only [Finset.image_empty] using
      HistoryIsometry.history_map e he loc F B ∅ v lam eta 0 P h.history
  · intro H hH
    obtain ⟨G,hG,rfl⟩ := List.mem_map.mp hH
    have hm : (G.map e).toFinset = G.toFinset.image e := by
      ext x
      simp only [List.mem_toFinset,List.mem_map,Finset.mem_image]
    rw [hm,HistoryIsometry.free_map]
    exact h.free_bound G hG
  · intro i hi
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hi
    have ha := HistoryIsometry.after_map e (∅ : Finset X) P
    simp only [Finset.image_empty] at ha
    rw [ha,HistoryIsometry.row_map e he]
    exact h.row x hx

lemma Attains.split {loc : D → X} {F B Q : Finset X} {v lam : ℝ} {q n c : ℕ}
    (h : Attains loc F B Q v lam q (n+1) c) :
    ∃ H, Valid loc F B Q v ((1+v^2)^q) lam 0 H ∧ (∀ i ∈ H, i ∈ F) ∧
      Attains loc F B (Q ∪ H.toFinset) v lam (q+1) n c := by
  obtain ⟨T,hT,hh,hr,hc⟩ := h
  cases T with
  | nil => simp at hT
  | cons H T =>
    cases hh with
    | cons hhead htail =>
      refine ⟨H,hhead,fun i hi => hr H (List.mem_cons_self) i hi,T,?_,htail,?_,hc⟩
      · simpa only [List.length_cons,Nat.add_right_cancel_iff] using hT
      · intro G hG
        exact hr G (List.mem_cons_of_mem _ hG)

def Finished (loc : D → X) (F : Finset X) (v eta lo hi : ℝ) (total k : ℕ) : Prop :=
  ∃ B lam P, Disjoint F B ∧ lo ≤ lam ∧ lam ≤ hi ∧
    PrefixData loc F B v lam eta total P ∧ ((after ∅ P) ∩ F).card = k

def Solved (loc : D → X) (F : Finset X) (v eta lo hi : ℝ) (total k : ℕ) : Prop :=
  ∃ (Y : Type uX) (m : PseudoMetricSpace Y) (d : DecidableEq Y) (e : X ↪ Y),
    letI := m
    letI := d
    (∀ x y, dist (e x) (e y) = dist x y) ∧
      Finished (fun j => e (loc j)) (F.image e) v eta lo hi total k

lemma Solved.of_finished {loc : D → X} {F : Finset X} {v eta lo hi : ℝ} {total k : ℕ}
    (h : Finished loc F v eta lo hi total k) : Solved loc F v eta lo hi total k := by
  refine ⟨X,inferInstance,inferInstance,Function.Embedding.refl X,fun _ _ => rfl,?_⟩
  change Finished loc (F.image (fun x => x)) v eta lo hi total k
  have he : F.image (fun x => x) = F := by ext x; simp
  rw [he]
  exact h

omit [DecidableEq X] in
lemma Solved.pullback {Y : Type uX} [PseudoMetricSpace Y] [DecidableEq Y]
    {loc : D → X} {F : Finset X} {v eta lo hi : ℝ} {total k : ℕ}
    (e : X ↪ Y) (he : ∀ x y, dist (e x) (e y) = dist x y)
    (h : Solved (fun j => e (loc j)) (F.image e) v eta lo hi total k) :
    Solved loc F v eta lo hi total k := by
  obtain ⟨Z,m,d,g,hg,hf⟩ := h
  let : PseudoMetricSpace Z := m
  let : DecidableEq Z := d
  refine ⟨Z,m,d,e.trans g,?_,?_⟩
  · intro x y
    exact (hg (e x) (e y)).trans (he x y)
  · change Finished (fun j => g (e (loc j))) (F.image (fun x => g (e x)))
      v eta lo hi total k
    simpa only [Finset.image_image,Function.comp_def] using hf

lemma PrefixData.finish {loc : D → X} {F B : Finset X} {v lam eta lo hi : ℝ}
    {q n k : ℕ} {P : List (List X)} (h : PrefixData loc F B v lam eta q P)
    (hv : 0 < v) (hvsmall : v < 1/6) (hlam : 0 < lam) (heta : 0 ≤ eta)
    (hdis : Disjoint F B) (hlow : lo ≤ lam) (hupp : lam ≤ hi)
    (hk : Attains loc F B (after ∅ P) v lam q n k) :
    Solved loc F v eta lo hi (q+n) k := by
  obtain ⟨T,hT,hh,hr,hc⟩ := hk
  apply Solved.of_finished
  refine ⟨B,lam,P++T,hdis,hlow,hupp,?_,?_⟩
  · simpa only [hT] using h.append_exact hv hvsmall hlam heta T hh hr
  · simpa only [after_append] using hc

end MetricKMedianRecovery.PhaseMergeInvariant

end OAI
