import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.ReachFar

namespace OAI

namespace MetricKMedianRecovery.PhaseSensitiveCrossing
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion PhaseMergeRefinement
  PhaseCountCrossing PhaseLengthInterpolation FreshCopyEndpoints
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

def LeafOutcome (loc : D → X) (F B Q : Finset X) (v lam eta : ℝ)
    (q n k N : ℕ) (U : ℚ) : Prop :=
  ∃ root ∈ F, ∃ H : List X, Good loc F B Q v ((1+v^2)^q) lam eta H ∧
    ((∃ s : ℚ, 0 ≤ s ∧ s ≤ U ∧ Reach loc F B Q root H v lam (q+1) n s k) ∨
      ∃ l u : ℚ, 0 ≤ l ∧ l ≤ u ∧ u ≤ U ∧ u-l ≤ 1/(2:ℚ)^(N+1) ∧
        ∃ c d, Sandwich k c d ∧ Reach loc F B Q root H v lam (q+1) n l c ∧
          Reach loc F B Q root H v lam (q+1) n u d)

theorem sensitive_search (loc : D → X) (F B Q : Finset X) (v lam eta : ℝ)
    (q n k N : ℕ) (M : ℚ) (hF : F.Nonempty) (hM : 0 < M) (hN : 3 ≤ N)
    (hv : 0 < v) (hvsmall : v < 1/6) (hlam : 0 < lam) (hlamUpper : lam ≤ 8*N*(M:ℝ))
    (hQ : Q ⊆ F ∪ B) (hdis : Disjoint F B)
    (hdiam : ∀ i ∈ F, ∀ j, dist i (loc j) ≤ (M:ℝ))
    (hrow : ∀ i ∈ F, bidRow loc (1-3*v) ((1+v^2)^q) Q i ≤ lam)
    (h : Sensitive loc F B Q v lam eta q n k) :
    LeafOutcome loc F B Q v lam eta q n k N (20*N*M) := by
  classical
  have hNr : (0:ℚ) < N := by exact_mod_cast (show 0 < N by omega)
  have hU : (0:ℚ) < 20*N*M := by positivity
  have hMr : (0:ℝ) < M := by exact_mod_cast hM
  have hUr : 20*N*(M:ℝ) ≤ ((20*N*M:ℚ):ℝ) := by norm_cast
  have ht : 0 ≤ 1-3*v := by linarith only [hvsmall]
  obtain ⟨H,G,hH,hG,he,a,b,hab,ha,hb⟩ := h
  cases he with
  | freeAppend H i f hi hf hd =>
    have hz : Reach loc F B Q i H v lam (q+1) n 0 b :=
      reach_zero_free loc F B Q i f H v lam eta (q+1) n b hdis hf hd ht hlam
        (by simpa only [Nat.add_sub_cancel] using hG.1) hb
    have hu := reach_far loc F B Q i H v lam M (q+1) n a N (20*N*M)
      hF hv hvsmall hlam hMr hN hlamUpper hUr hdiam
      (advance_rows loc F B Q v lam eta q H hv hvsmall hlam hrow hH.1) ha
    exact ⟨i,hi,H,hH,search loc F B Q i H v lam (q+1) n k (N+1) b a (20*N*M) hU
      (Finset.union_subset hQ hH.1.1.opened_subset) hz hu hab.symm⟩
  | paidDelete C T i hi =>
    obtain ⟨c,hc,hac⟩ := reach_zero_paid loc F B Q i C T v lam eta (q+1) n a hi hdis ht hlam
      (by simpa only [Nat.add_sub_cancel] using hH.1) ha
    refine ⟨i,hi,C++T,hG,?_⟩
    by_cases hck : c = k
    · exact Or.inl ⟨0,le_rfl,hU.le,hck ▸ hc⟩
    · have hcb : Sandwich k c b := by
        rcases hab with ⟨hak,hkb⟩ | ⟨hbk,hka⟩
        · exact Or.inl ⟨by omega,hkb⟩
        · exact Or.inr ⟨hbk,by omega⟩
      have hu := reach_far loc F B Q i (C++T) v lam M (q+1) n b N (20*N*M)
        hF hv hvsmall hlam hMr hN hlamUpper hUr hdiam
        (advance_rows loc F B Q v lam eta q (C++T) hv hvsmall hlam hrow hG.1) hb
      exact search loc F B Q i (C++T) v lam (q+1) n k (N+1) c b (20*N*M) hU
        (Finset.union_subset hQ hG.1.1.opened_subset) hc hu hcb

theorem three_free_phase (loc : D → X) (F B Q : Finset X) (root : X) (H : List X)
    (v lam eta : ℝ) (q : ℕ) (hv : 0 < v) (hvsmall : v < 1/6) (hlam : 0 < lam)
    (hrow : ∀ i ∈ F, bidRow loc (1-3*v) ((1+v^2)^q) Q i ≤ lam)
    (hH : Good loc F B Q v ((1+v^2)^q) lam eta H) (s : ℝ) :
    letI : PseudoMetricSpace (X ⊕ ℝ) := familyMetric root
    Valid (fun j => incl (loc j)) (F.image incl) (insert (Sum.inr s) (B.image incl))
      (Q.image incl) v ((1+v^2)^q) lam eta (leafPhase H s) ∧
      ((leafPhase H s).toFinset \ F.image incl).card ≤ 3 := by
  classical
  refine ⟨leaf_valid loc F B Q root H v lam eta q hv hvsmall hlam hrow hH.1 s,?_⟩
  rw [leaf_free_count]
  have hh := hH.2
  omega

end MetricKMedianRecovery.PhaseSensitiveCrossing

namespace MetricKMedianRecovery.PhaseFreshAllocation
open PhaseSequence PhaseMergePath PhaseMergeCompletion PhaseCountCrossing
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

def incl : X ↪ X ⊕ (X × Bool) := ⟨Sum.inl,Sum.inl_injective⟩

@[instance_reducible]
noncomputable def enlargedMetric : PseudoMetricSpace (X ⊕ (X × Bool)) :=
  LeafMetric.attachedMetric Prod.fst (fun _ => 0) (fun _ => le_rfl)

noncomputable def copy (b : Bool) : X ⊕ (X × Bool) → X ⊕ (X × Bool) :=
  Sum.elim (fun x => Sum.inr (x,b)) Sum.inr

omit [Fintype D] [DecidableEq X] in
lemma original_dist (x y : X) :
    letI : PseudoMetricSpace (X ⊕ (X × Bool)) := enlargedMetric
    dist (incl x) (incl y) = dist x y :=
  LeafMetric.original_distance _ _ x y

omit [Fintype D] [DecidableEq X] in
lemma copy_dist (x y : X) (b : Bool) :
    letI : PseudoMetricSpace (X ⊕ (X × Bool)) := enlargedMetric
    dist (incl x) (copy b (incl y)) = dist x y := by
  change LeafMetric.leafDist Prod.fst (fun _ => 0) (Sum.inl x) (Sum.inr (y,b)) = _
  rw [LeafMetric.copy_distance]
  exact add_zero _

omit [Fintype D] [PseudoMetricSpace X] in
lemma copy_fresh (F B : Finset X) (i : X ⊕ (X × Bool)) (hi : i ∈ F.image incl)
    (b : Bool) : copy b i ∉ F.image incl ∪ B.image incl := by
  obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp hi
  simp [copy,incl]

omit [Fintype D] [PseudoMetricSpace X] in
lemma spare_fresh (F B : Finset X) (i : X ⊕ (X × Bool)) (hi : i ∈ F.image incl) :
    copy true i ∉ F.image incl ∪ pool (F.image incl) (B.image incl) (copy false) := by
  obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp hi
  simp only [pool,Finset.mem_union,Finset.mem_image]
  rintro (⟨y,_,h⟩ | ⟨y,_,h⟩ | ⟨j,⟨y,_,rfl⟩,h⟩) <;> simp [copy,incl] at h

omit [Fintype D] [PseudoMetricSpace X] in
lemma disjoint_image (F B : Finset X) (hdis : Disjoint F B) :
    Disjoint (F.image (incl : X ↪ X ⊕ (X × Bool))) (B.image incl) := by
  rw [Finset.disjoint_left]
  intro x hx hy
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨j,hj,hji⟩ := Finset.mem_image.mp hy
  exact Finset.disjoint_left.mp hdis hi (incl.injective hji ▸ hj)

theorem allocated_crossing (loc : D → X) (F B Q : Finset X)
    (v lam eta : ℝ) (q n k a b : ℕ) (hv : 0 < v) (hvsmall : v < 1/6)
    (hlam : 0 < lam) (heta : 0 ≤ eta) (hQ : Q ⊆ F ∪ B) (hdis : Disjoint F B)
    (hrow : ∀ i ∈ F, bidRow loc (1-3*v) ((1+v^2)^q) Q i ≤ lam)
    (H G : List X) (hH : Valid loc F B Q v ((1+v^2)^q) lam eta H)
    (hG : Valid loc F B Q v ((1+v^2)^q) lam eta G)
    (hHr : ∀ i ∈ H, i ∈ F) (hGr : ∀ i ∈ G, i ∈ F) (hab : Sandwich k a b)
    (ha : Attains loc F B (Q ∪ H.toFinset) v lam (q+1) n a)
    (hb : Attains loc F B (Q ∪ G.toFinset) v lam (q+1) n b) :
    letI : PseudoMetricSpace (X ⊕ (X × Bool)) := enlargedMetric
    Outcome (fun j => incl (loc j)) (F.image incl)
      (pool (F.image incl) (pool (F.image incl) (B.image incl) (copy false)) (copy true))
      (Q.image incl) v lam eta q n k := by
  classical
  let : PseudoMetricSpace (X ⊕ (X × Bool)) := enlargedMetric
  apply regular_phase_crossing _ _ _ _ (copy false) (copy true) v lam eta q n k a b
    hv hvsmall hlam heta (H := H.map incl) (G := G.map incl)
  · simpa only [Finset.image_union] using Finset.image_subset_image (f := (incl : X ↪ _)) hQ
  · exact disjoint_image F B hdis
  · intro i hi
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hi
    rw [HistoryIsometry.row_map incl original_dist]
    exact hrow x hx
  · exact fun i hi => copy_fresh F B i hi false
  · intro i hi j
    obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp hi
    rw [original_dist,copy_dist]
  · exact spare_fresh F B
  · intro i hi j
    obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp hi
    rw [original_dist,copy_dist]
  · exact HistoryIsometry.valid_map incl original_dist loc F B Q v _ lam eta H hH
  · exact HistoryIsometry.valid_map incl original_dist loc F B Q v _ lam eta G hG
  · intro i hi
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hi
    exact Finset.mem_image.mpr ⟨x,hHr x hx,rfl⟩
  · intro i hi
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hi
    exact Finset.mem_image.mpr ⟨x,hGr x hx,rfl⟩
  · exact hab
  · simpa only [HistoryIsometry.image_union] using ha.map incl original_dist
  · simpa only [HistoryIsometry.image_union] using hb.map incl original_dist

end MetricKMedianRecovery.PhaseFreshAllocation

end OAI
