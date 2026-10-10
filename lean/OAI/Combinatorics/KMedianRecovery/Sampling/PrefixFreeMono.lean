import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.SwapOriginal

namespace OAI

namespace MetricKMedianRecovery.CommonPrefixTransfer
open PhaseHistoryTransfer FreshCopyEndpoints FreshLeafTransfer
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

lemma prefix_free_mono (loc : D → X) (F B B' Q : Finset X)
    (v z lam eta : ℝ) (H : List X) (hBB : B ⊆ B')
    (hh : PhaseSequence.Prefix loc F B v z lam eta Q H) :
    PhaseSequence.Prefix loc F B' v z lam eta Q H := by
  induction hh with
  | nil Q => exact PhaseSequence.Prefix.nil Q
  | @cons Q i H hi htail ih =>
    apply PhaseSequence.Prefix.cons _ ih
    refine ⟨hi.1,?_⟩
    rcases hi.2 with hb|⟨hF,W,hQ,hW,hop⟩
    · exact Or.inl (hBB hb)
    · exact Or.inr ⟨hF,W,hQ,hW.trans (Finset.union_subset_union_right hBB),hop⟩

lemma history_free_mono (loc : D → X) (F B B' Q : Finset X)
    (v lam eta : ℝ) (q : ℕ) (T : List (List X)) (hBB : B ⊆ B')
    (hh : History loc F B v lam eta q Q T) : History loc F B' v lam eta q Q T := by
  induction hh with
  | nil q Q => exact History.nil q Q
  | @cons q Q H T hhead htail ih =>
    exact History.cons ⟨prefix_free_mono loc F B B' Q v _ lam eta H hBB hhead.1,hhead.2⟩ ih

lemma history_rows (loc : D → X) (F B Q : Finset X) (v lam eta : ℝ)
    (q : ℕ) (T : List (List X)) (hv : 0 < v) (hvsmall : v < 1/6) (hlam : 0 < lam)
    (hrow : ∀ i ∈ F, bidRow loc (1-3*v) ((1+v^2)^q) Q i ≤ lam)
    (hh : History loc F B v lam eta q Q T) :
    ∀ i ∈ F, bidRow loc (1-3*v) ((1+v^2)^(q+T.length)) (after Q T) i ≤ lam := by
  induction hh with
  | nil q Q => simpa only [List.length_nil,Nat.add_zero,after] using hrow
  | @cons q Q H T hhead htail ih =>
    have hr := ih (advance_rows loc F B Q v lam eta q H hv hvsmall hlam hrow hhead)
    simpa only [after,List.length_cons,Nat.add_right_comm,Nat.add_assoc] using hr

lemma history_append (loc : D → X) (F B Q : Finset X) (v lam eta : ℝ)
    (q : ℕ) (P T : List (List X)) (hp : History loc F B v lam eta q Q P)
    (ht : History loc F B v lam eta (q+P.length) (after Q P) T) :
    History loc F B v lam eta q Q (P++T) := by
  induction hp with
  | nil q Q => simpa only [List.nil_append,List.length_nil,Nat.add_zero,after] using ht
  | @cons q Q H P hhead htail ih =>
    apply History.cons hhead
    apply ih
    simpa only [after,List.length_cons,Nat.add_right_comm,Nat.add_assoc] using ht

theorem current_phase (loc : D → X) (F B : Finset X) (i : X)
    (u s v lam eta : ℝ) (hs : 0 ≤ s) (hsu : s ≤ u)
    (hv : 0 < v) (hvsmall : v < 1/6) (hlam : 0 < lam)
    (herror : (Fintype.card D:ℝ)*((1-3*v)*(u-s)) ≤ (Fintype.card D:ℝ)*eta)
    (hfar : ∀ j, ∀ x ∈ F, 1 ≤ dist x (loc j))
    (P : List (List X)) (hp : History loc F B v lam eta 0 ∅ P) :
    letI : PseudoMetricSpace (X ⊕ ℝ) := familyMetric i
    ∀ H : List (X ⊕ ℝ),
      PhaseSequence.Valid (fun j => incl (loc j)) (F.image incl)
        (insert (Sum.inr u) (B.image incl)) ((after ∅ P).image incl)
        v ((1+v^2)^P.length) lam 0 H →
      History (fun j => incl (loc j)) (F.image incl) (insert (Sum.inr s) (B.image incl))
        v lam eta 0 ∅ ((P.map (List.map incl))++[H.map (Equiv.swap (Sum.inr u) (Sum.inr s))]) := by
  classical
  let : PseudoMetricSpace (X ⊕ ℝ) := familyMetric i
  intro H hH
  let Q := after ∅ P
  have hQ : Q ⊆ F ∪ B := hp.after_subset (Finset.empty_subset _)
  have hr : ∀ x y : X, dist (incl x) (incl y) = dist x y := original_dist i
  have hrow0 : ∀ x ∈ F, bidRow loc (1-3*v) ((1+v^2)^0) ∅ x ≤ lam := by
    intro x hx
    have he : bidRow loc (1-3*v) ((1+v^2)^0) ∅ x = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      simp only [clippedAt,Finset.not_nonempty_empty,↓reduceIte,pow_zero]
      exact max_eq_right (by linarith only [hfar j x hx])
    rw [he]
    exact hlam.le
  have hrow := history_rows loc F B ∅ v lam eta 0 P hv hvsmall hlam hrow0 hp
  simp only [Nat.zero_add] at hrow
  have hrow' : ∀ x ∈ F.image (incl : X ↪ X ⊕ ℝ),
      bidRow (fun j => incl (loc j)) (1-3*v) ((1+v^2)^P.length) (Q.image incl ∪ H.toFinset) x ≤ lam := by
    intro x hx
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
    apply le_trans (bidRow_antitone_open (fun j => incl (loc j)) (1-3*v)
      ((1+v^2)^P.length) (Q.image incl) (Q.image incl ∪ H.toFinset) (incl a)
      (by linarith only [hvsmall]) Finset.subset_union_left)
    unfold bidRow
    have hc : ∀ j, clippedAt (fun j => incl (loc j)) (1-3*v) ((1+v^2)^P.length) (Q.image incl) j =
        clippedAt loc (1-3*v) ((1+v^2)^P.length) Q j := by
      intro j
      unfold clippedAt
      simp only [Finset.image_nonempty,HistoryIsometry.nearest_map incl hr]
    simp only [hc,hr]
    exact hrow a ha
  have hfix : ∀ x ∈ F.image (incl : X ↪ X ⊕ ℝ),
      Equiv.swap (Sum.inr u) (Sum.inr s) x = x := by
    intro x hx
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
    exact swap_original u s a
  have hQ' : Q.image (incl : X ↪ X ⊕ ℝ) ⊆
      F.image incl ∪ insert (Sum.inr u) (B.image incl) := by
    intro x hx
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
    rcases Finset.mem_union.mp (hQ ha) with ha|ha
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨a,ha,rfl⟩)
    · exact Finset.mem_union_right _ (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨a,ha,rfl⟩))
  have hmap := PhaseParameterTransfer.valid_map (fun j => incl (loc j)) (F.image incl)
    (insert (Sum.inr u) (B.image incl)) (Q.image incl) H (Equiv.swap (Sum.inr u) (Sum.inr s))
    v ((1+v^2)^P.length) lam lam eta (u-s) hv hvsmall (by positivity) hlam
    (sub_nonneg.mpr hsu) le_rfl (by simpa only [sub_self,zero_add] using herror)
    (Equiv.swap _ _).injective hfix hQ'
    (fun j y hy => (shortening i (loc j) F B u s hs hsu y hy).1)
    (fun j y hy => (shortening i (loc j) F B u s hs hsu y hy).2) hrow' hH
  rw [image_copy,image_original] at hmap
  have hp' : History (fun j => incl (loc j)) (F.image incl) (B.image incl)
      v lam eta 0 ∅ (P.map (List.map incl)) := by
    simpa only [Finset.image_empty] using HistoryIsometry.history_map incl hr loc F B ∅ v lam eta 0 P hp
  have hp'' := history_free_mono (fun j => incl (loc j)) (F.image incl) (B.image incl)
    (insert (Sum.inr s) (B.image incl)) ∅ v lam eta 0 (P.map (List.map incl))
    (Finset.subset_insert _ _) hp'
  apply history_append (fun j => incl (loc j)) (F.image incl) (insert (Sum.inr s) (B.image incl))
    ∅ v lam eta 0 (P.map (List.map incl)) _ hp''
  have hafter : after ∅ (P.map (List.map incl)) = Q.image incl := by
    simpa only [Finset.image_empty] using HistoryIsometry.after_map incl (∅ : Finset X) P
  rw [hafter,List.length_map,Nat.zero_add]
  exact History.cons hmap (History.nil _ _)

end MetricKMedianRecovery.CommonPrefixTransfer

end OAI
