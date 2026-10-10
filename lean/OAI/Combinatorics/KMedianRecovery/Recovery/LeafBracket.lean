import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.LeafOutcome
import OAI.Combinatorics.KMedianRecovery.Recovery.Coupled

namespace OAI

namespace MetricKMedianRecovery.PhaseLeafCoupling
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion PhaseCountCrossing PhaseMergeInvariant
  PhaseMergeRefinement PhaseCoupledMerge PhaseLengthInterpolation FreshCopyEndpoints PhaseSensitiveCrossing
universe uD uX
variable {D : Type uD} {X : Type uX} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

omit [Fintype D] [PseudoMetricSpace X] in
lemma disjoint_leaf (F B : Finset X) (hd : Disjoint F B) (s : ℝ) :
    Disjoint (F.image (incl : X ↪ X ⊕ ℝ)) (insert (Sum.inr s) (B.image incl)) := by
  rw [Finset.disjoint_insert_right]
  refine ⟨by simp [incl],?_⟩
  rw [Finset.disjoint_left]
  intro x hx hy
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨j,hj,he⟩ := Finset.mem_image.mp hy
  exact Finset.disjoint_left.mp hd hi (incl.injective he ▸ hj)

lemma prefix_leaf {loc : D → X} {F B : Finset X} {v lam eta : ℝ} {q : ℕ}
    {P : List (List X)} (hp : PrefixData loc F B v lam eta q P)
    (hv : 0 < v) (hvsmall : v < 1/6) (hlam : 0 < lam)
    (root : X) (H : List X)
    (hH : Good loc F B (after ∅ P) v ((1+v^2)^q) lam eta H) (s : ℝ) :
    letI : PseudoMetricSpace (X ⊕ ℝ) := familyMetric root
    PrefixData (fun j => incl (loc j)) (F.image incl) (insert (Sum.inr s) (B.image incl))
      v lam eta (q+1) (P.map (List.map incl)++[leafPhase H s]) := by
  classical
  let : PseudoMetricSpace (X ⊕ ℝ) := familyMetric root
  have hp' := (hp.map incl (original_dist root)).mono_free
    (Finset.subset_insert (Sum.inr s) (B.image incl))
  obtain ⟨hh,hf⟩ := three_free_phase loc F B (after ∅ P) root H v lam eta q
    hv hvsmall hlam hp.row hH s
  have he := HistoryIsometry.after_map (incl : X ↪ X ⊕ ℝ) (∅ : Finset X) P
  simp only [Finset.image_empty] at he
  exact hp'.append_phase hv hvsmall hlam (leafPhase H s) (by rw [he]; exact hh) hf

omit [Fintype D] [PseudoMetricSpace X] in
lemma prefix_swap (P : List (List X)) (H : List X) (u l : ℝ) :
    (P.map (List.map incl)++[leafPhase H u]).map
      (List.map (Equiv.swap (Sum.inr u) (Sum.inr l))) =
      P.map (List.map incl)++[leafPhase H l] := by
  classical
  simp only [List.map_append,List.map_cons,List.map_nil,leafPhase,List.map_map,
    Function.comp_def,FreshLeafTransfer.swap_original,Equiv.swap_apply_left]

lemma reach_after {loc : D → X} {F B : Finset X} {v lam : ℝ} {q n c : ℕ}
    (root : X) (P : List (List X)) (H : List X) (s : ℚ)
    (hc : Reach loc F B (after ∅ P) root H v lam (q+1) n s c) :
    letI : PseudoMetricSpace (X ⊕ ℝ) := familyMetric root
    Attains (fun j => incl (loc j)) (F.image incl) (insert (Sum.inr (s:ℝ)) (B.image incl))
      (after ∅ (P.map (List.map incl)++[leafPhase H s])) v lam (q+1) n c := by
  classical
  let : PseudoMetricSpace (X ⊕ ℝ) := familyMetric root
  have he := HistoryIsometry.after_map (incl : X ↪ X ⊕ ℝ) (∅ : Finset X) P
  simp only [Finset.image_empty] at he
  simpa only [Reach,after_append,after,he,leaf_boundary] using hc

theorem leaf_success {loc : D → X} {F B : Finset X} {v lam eta lo hi : ℝ} {q n k : ℕ}
    {P : List (List X)} (hp : PrefixData loc F B v lam eta q P)
    (hv : 0 < v) (hvsmall : v < 1/6) (hlam : 0 < lam) (heta : 0 ≤ eta)
    (hd : Disjoint F B) (hl : lo ≤ lam) (hu : lam ≤ hi)
    (root : X) (H : List X)
    (hH : Good loc F B (after ∅ P) v ((1+v^2)^q) lam eta H) (s : ℚ)
    (hc : Reach loc F B (after ∅ P) root H v lam (q+1) n s k) :
    Solved loc F v eta lo hi (q+(n+1)) k := by
  classical
  let : PseudoMetricSpace (X ⊕ ℝ) := familyMetric root
  have hp' := prefix_leaf hp hv hvsmall hlam root H hH s
  have hc' := reach_after root P H s hc
  have hs := hp'.finish hv hvsmall hlam heta (disjoint_leaf F B hd s) hl hu hc'
  have hs' := Solved.pullback (incl : X ↪ X ⊕ ℝ) (original_dist root) hs
  simpa only [Nat.add_assoc,Nat.add_comm 1 n] using hs'

noncomputable def leaf_bracket {loc : D → X} {F B : Finset X} {v lam eta lo hi : ℝ}
    {q n k a b : ℕ} {P : List (List X)} (hp : PrefixData loc F B v lam eta q P)
    (hv : 0 < v) (hvsmall : v < 1/6) (hlam : 0 < lam)
    (hd : Disjoint F B) (hl : lo ≤ lam) (hu : lam ≤ hi)
    (root : X) (H : List X)
    (hH : Good loc F B (after ∅ P) v ((1+v^2)^q) lam eta H)
    (l u : ℚ) (hl0 : 0 ≤ l) (hlu : l ≤ u) (hwidth : (u:ℝ)-(l:ℝ) ≤ eta)
    (hs : Sandwich k a b)
    (ha : Reach loc F B (after ∅ P) root H v lam (q+1) n l a)
    (hb : Reach loc F B (after ∅ P) root H v lam (q+1) n u b) :
    letI : PseudoMetricSpace (X ⊕ ℝ) := familyMetric root
    Coupled (fun j => incl (loc j)) (F.image incl) v eta lo hi (q+1) n k := by
  classical
  let : PseudoMetricSpace (X ⊕ ℝ) := familyMetric root
  have heps : (0:ℝ) ≤ (u:ℝ)-(l:ℝ) := by exact_mod_cast sub_nonneg.mpr hlu
  have hlr : (0:ℝ) ≤ l := by exact_mod_cast hl0
  have hlur : (l:ℝ) ≤ u := by exact_mod_cast hlu
  refine {
    B := insert (Sum.inr (u:ℝ)) (B.image incl)
    P := P.map (List.map incl)++[leafPhase H u]
    r := Equiv.swap (Sum.inr (u:ℝ)) (Sum.inr (l:ℝ))
    lam := lam
    lam' := lam
    eps := (u:ℝ)-(l:ℝ)
    a := a
    b := b
    disjoint := disjoint_leaf F B hd u
    low := hl
    high := hu
    price := le_rfl
    eps_nonneg := heps
    error := ?_
    inj := (Equiv.swap _ _).injective
    fixed := ?_
    shrink := ?_
    loss := ?_
    old_prefix := prefix_leaf hp hv hvsmall hlam root H hH u
    new_prefix := ?_
    sandwich := hs
    new_tail := ?_
    old_tail := reach_after root P H u hb }
  · simp only [sub_self,zero_add]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    nlinarith only [hv,heps,hwidth]
  · intro i hi
    obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp hi
    exact FreshLeafTransfer.swap_original u l x
  · intro j x hx
    exact (FreshLeafTransfer.shortening root (loc j) F B u l hlr hlur x hx).1
  · intro j x hx
    exact (FreshLeafTransfer.shortening root (loc j) F B u l hlr hlur x hx).2
  · simpa only [FreshLeafTransfer.image_copy,prefix_swap] using
      prefix_leaf hp hv hvsmall hlam root H hH l
  · simpa only [FreshLeafTransfer.image_copy,prefix_swap] using reach_after root P H l ha

end MetricKMedianRecovery.PhaseLeafCoupling

end OAI
