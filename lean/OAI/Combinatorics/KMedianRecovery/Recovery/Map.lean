import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.MergeCross
import OAI.Combinatorics.KMedianRecovery.Geometry.FamilyMetric

namespace OAI

namespace MetricKMedianRecovery.PhaseMergeCompletion
open PhaseHistoryTransfer
variable {D X Y : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]
  [PseudoMetricSpace Y] [DecidableEq Y]

lemma Attains.map {loc : D → X} {F B Q : Finset X} {v lam : ℝ} {q n c : ℕ}
    (h : Attains loc F B Q v lam q n c) (r : X ↪ Y)
    (hr : ∀ x y, dist (r x) (r y) = dist x y) :
    Attains (fun j => r (loc j)) (F.image r) (B.image r) (Q.image r) v lam q n c := by
  obtain ⟨T,hT,hh,hreg,hc⟩ := h
  refine ⟨T.map (List.map r),by simpa only [List.length_map] using hT,
    HistoryIsometry.history_map r hr loc F B Q v lam 0 q T hh,?_,?_⟩
  · rintro H hH x hx
    obtain ⟨G,hG,rfl⟩ := List.mem_map.mp hH
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx
    exact Finset.mem_image.mpr ⟨i,hreg G hG i hi,rfl⟩
  · rw [HistoryIsometry.after_map,HistoryIsometry.paid_map]
    exact hc

lemma Attains.insert_disabled {loc : D → X} {F B Q : Finset X} {v lam : ℝ} {q n c : ℕ}
    (h : Attains loc F B Q v lam q n c) (f : X) (hv : v < 1/6)
    (hf : f ∉ F ∪ B)
    (hfar : ∀ r, r < n → ∀ j, (1+v^2)*(1+v^2)^(q+r) < (1-3*v)*dist (loc j) f) :
    Attains loc F (insert f B) (insert f Q) v lam q n c := by
  obtain ⟨T,hT,hh,hr,hc⟩ := h
  refine ⟨T,hT,DisablingHistory.history_insert loc F B Q v lam 0 f q T hv hf
    (by simpa only [hT] using hfar) hh,hr,?_⟩
  rw [DisablingHistory.after_insert]
  have hfF : f ∉ F := fun he => hf (Finset.mem_union_left _ he)
  rw [Finset.insert_inter_of_notMem hfF]
  exact hc

lemma Attains.swap_free {loc : D → X} {F B Q : Finset X} {v lam : ℝ} {q n c : ℕ}
    (h : Attains loc F B Q v lam q n c) (i f : X) (hi : i ∉ F) (hf : f ∉ F ∪ B)
    (hd : ∀ j, dist (loc j) i = dist (loc j) f) (ht : 0 ≤ 1-3*v) (hlam : 0 < lam) :
    Attains loc F (insert f B) (Q.image (Equiv.swap i f)) v lam q n c := by
  obtain ⟨T,hT,hh,hreg,hc⟩ := h
  have hfix : ∀ x ∈ F, Equiv.swap i f x = x := by
    intro x hx
    exact Equiv.swap_apply_of_ne_of_ne (fun he => hi (he ▸ hx))
      (fun he => hf (Finset.mem_union_left _ (he ▸ hx)))
  have hF : F.image (Equiv.swap i f) = F := by
    calc
      F.image (Equiv.swap i f) = F.image id := Finset.image_congr hfix
      _ = F := Finset.image_id
  refine ⟨T.map (List.map (Equiv.swap i f)),by simpa only [List.length_map] using hT,
    CoincidentHistory.history_swap loc F B Q v lam 0 i f hf hd ht hlam q T hh,?_,?_⟩
  · rintro H hH x hx
    obtain ⟨G,hG,rfl⟩ := List.mem_map.mp hH
    obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hx
    rw [hfix y (hreg G hG y hy)]
    exact hreg G hG y hy
  · rw [HistoryIsometry.after_map,← hF,
      ← Finset.image_inter _ _ (Equiv.swap i f).injective,
      Finset.card_image_of_injective _ (Equiv.swap i f).injective]
    exact hc

end MetricKMedianRecovery.PhaseMergeCompletion

namespace MetricKMedianRecovery.PhaseLengthInterpolation
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion FreshCopyEndpoints
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

def leafPhase (H : List X) (s : ℝ) : List (X ⊕ ℝ) := H.map incl ++ [Sum.inr s]

omit [PseudoMetricSpace X] in
lemma leaf_boundary (Q : Finset X) (H : List X) (s : ℝ) :
    Q.image incl ∪ (leafPhase H s).toFinset = insert (Sum.inr s) ((Q ∪ H.toFinset).image incl) := by
  classical
  simp only [leafPhase,List.toFinset_append,List.toFinset_cons,List.toFinset_nil,
    Finset.union_insert,Finset.union_empty,HistoryIsometry.image_union]

theorem leaf_valid (loc : D → X) (F B Q : Finset X) (i : X) (H : List X)
    (v lam eta : ℝ) (q : ℕ) (hv : 0 < v) (hvsmall : v < 1/6) (hlam : 0 < lam)
    (hrow : ∀ x ∈ F, bidRow loc (1-3*v) ((1+v^2)^q) Q x ≤ lam)
    (hH : Valid loc F B Q v ((1+v^2)^q) lam eta H) (s : ℝ) :
    letI : PseudoMetricSpace (X ⊕ ℝ) := familyMetric i
    Valid (fun j => incl (loc j)) (F.image incl) (insert (Sum.inr s) (B.image incl))
      (Q.image incl) v ((1+v^2)^q) lam eta (leafPhase H s) := by
  classical
  let : PseudoMetricSpace (X ⊕ ℝ) := familyMetric i
  have hh := HistoryIsometry.valid_map incl (original_dist i) loc F B Q v ((1+v^2)^q) lam eta H hH
  refine PhaseMergeSurgery.append_free _ _ _ _ _ _ _ _ hv hvsmall (by positivity) hlam ?_ _ hh _ ?_
  · intro x hx
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
    unfold bidRow
    have hc : ∀ j, clippedAt (fun j => incl (loc j)) (1-3*v) ((1+v^2)^q) (Q.image incl) j =
        clippedAt loc (1-3*v) ((1+v^2)^q) Q j := by
      intro j
      unfold clippedAt
      simp only [Finset.image_nonempty,HistoryIsometry.nearest_map incl (original_dist i)]
    simpa only [bidRow,hc,original_dist i] using hrow y hy
  · simp [incl]

omit [PseudoMetricSpace X] in
lemma leaf_free_count (F : Finset X) (H : List X) (s : ℝ) :
    ((leafPhase H s).toFinset \ F.image incl).card = (H.toFinset \ F).card+1 := by
  classical
  have hf : Sum.inr s ∉ F.image (incl : X ↪ X ⊕ ℝ) := by simp [incl]
  have hH : Sum.inr s ∉ H.toFinset.image (incl : X ↪ X ⊕ ℝ) := by simp [incl]
  have hm : (H.map (incl : X ↪ X ⊕ ℝ)).toFinset = H.toFinset.image incl := by
    simpa only [Finset.image_empty,Finset.empty_union] using
      HistoryIsometry.image_union (incl : X ↪ X ⊕ ℝ) ∅ H
  simp only [leafPhase,List.toFinset_append,List.toFinset_cons,List.toFinset_nil,
    Finset.union_insert,Finset.union_empty,hm]
  rw [Finset.insert_sdiff_of_notMem _ hf,Finset.card_insert_of_notMem
    (fun h => hH (Finset.mem_sdiff.mp h).1),HistoryIsometry.free_map]

theorem leaf_attains (loc : D → X) (F B Q : Finset X) (i : X) (H : List X)
    (v lam : ℝ) (q n : ℕ) (hQ : Q ∪ H.toFinset ⊆ F ∪ B) (s : ℝ) :
    letI : PseudoMetricSpace (X ⊕ ℝ) := familyMetric i
    ∃ c, Attains (fun j => incl (loc j)) (F.image incl) (insert (Sum.inr s) (B.image incl))
      (insert (Sum.inr s) ((Q ∪ H.toFinset).image incl)) v lam q n c := by
  classical
  let : PseudoMetricSpace (X ⊕ ℝ) := familyMetric i
  apply attains_exists
  intro x hx
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact Finset.mem_union_right _ (Finset.mem_insert_self _ _)
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
  rcases Finset.mem_union.mp (hQ hy) with hy | hy
  · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨y,hy,rfl⟩)
  · exact Finset.mem_union_right _ (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨y,hy,rfl⟩))

end MetricKMedianRecovery.PhaseLengthInterpolation

end OAI
