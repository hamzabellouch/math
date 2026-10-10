import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.LeafOrder

namespace OAI

namespace MetricKMedianRecovery.RationalLeaves
open PhaseSequence PhaseHistoryTransfer PhaseMergeInvariant PhaseMergeRefinement
variable {V : Type*} [DecidableEq V] {d : ℕ}

lemma shorten_allowed (F : Finset V) (B : Finset (Label V)) (key : ℕ) (hB : Before key B)
    (i : V) (l u : ℚ) (x : Label V) (hx : x∈F.image original∪B) : shorten key i l u x=x := by
  rcases Finset.mem_union.mp hx with hx|hx
  · obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hx
    exact shorten_original key i j l u
  · exact shorten_old key i l u B hB x hx

lemma shorten_image (B : Finset (Label V)) (key : ℕ) (hB : Before key B) (i : V) (l u : ℚ) :
    (B.image (shorten key i l u))=B := by
  calc
    _=B.image id := Finset.image_congr (shorten_old key i l u B hB)
    _=B := Finset.image_id

lemma shorten_insert (B : Finset (Label V)) (key : ℕ) (hB : Before key B) (i : V) (l u : ℚ) :
    (insert (leaf key i u) B).image (shorten key i l u)=insert (leaf key i l) B := by
  rw [Finset.image_insert,shorten_image B key hB i l u,shorten,Equiv.swap_apply_left]

variable [PseudoMetricSpace V]
attribute [local instance] RationalLeaves.metric

lemma history_allowed {loc : Fin d → V} {F : Finset V} {B Q : Finset (Label V)}
    {v lam eta : ℝ} {q : ℕ} {P : List (List (Label V))}
    (h : History (fun j=>original (loc j)) (F.image original) B v lam eta q Q P) :
    ∀ H∈P,H.toFinset⊆F.image original∪B := by
  induction h with
  | nil => simp
  | @cons q Q H T hH hT ih =>
    intro G hG
    rcases List.mem_cons.mp hG with rfl|hG
    · exact hH.1.opened_subset
    · exact ih G hG

lemma history_shorten {loc : Fin d → V} {F : Finset V} {B Q : Finset (Label V)}
    {v lam eta : ℝ} {q : ℕ} {P : List (List (Label V))}
    (h : History (fun j=>original (loc j)) (F.image original) B v lam eta q Q P)
    (key : ℕ) (hB : Before key B) (i : V) (l u : ℚ) :
    P.map (List.map (shorten key i l u))=P := by
  calc
    _=P.map id := List.map_congr_left (by
      intro H hH
      change H.map (shorten key i l u)=H
      calc
        _=H.map id := List.map_congr_left (fun x hx=>shorten_allowed F B key hB i l u x
          (history_allowed h H hH (List.mem_toFinset.mpr hx)))
        _=H := List.map_id H)
    _=P := List.map_id P

lemma prefix_shorten {loc : Fin d → V} {F : Finset V} {B : Finset (Label V)}
    {v lam eta : ℝ} {q : ℕ} {P : List (List (Label V))}
    (hp : PrefixData (fun j=>original (loc j)) (F.image original) B v lam eta q P)
    (key : ℕ) (hB : Before key B) (i : V) (l u : ℚ) (H : List (Label V))
    (hH : H.toFinset⊆F.image original∪B) :
    (P++[H++[leaf key i u]]).map (List.map (shorten key i l u))=P++[H++[leaf key i l]] := by
  have hm : H.map (shorten key i l u)=H := by
    calc
      _=H.map id := List.map_congr_left (fun x hx=>shorten_allowed F B key hB i l u x (hH (List.mem_toFinset.mpr hx)))
      _=H := List.map_id H
  simp only [List.map_append,List.map_cons,List.map_nil,history_shorten hp.history key hB i l u,hm]
  rw [shorten,Equiv.swap_apply_left]

lemma prefix_leaf {loc : Fin d → V} {F : Finset V} {B : Finset (Label V)}
    {v lam eta : ℝ} {q : ℕ} {P : List (List (Label V))}
    (hp : PrefixData (fun j=>original (loc j)) (F.image original) B v lam eta q P)
    (key : ℕ) (hB : Before key B) (i : V) (s : ℚ) (hv : 0<v) (hv1 : v<1/6) (hlam : 0<lam)
    (H : List (Label V))
    (hH : Good (fun j=>original (loc j)) (F.image original) B (after ∅ P) v ((1+v^2)^q) lam eta H) :
    PrefixData (fun j=>original (loc j)) (F.image original) (insert (leaf key i s) B) v lam eta (q+1)
      (P++[H++[leaf key i s]]) := by
  obtain ⟨hh,hcount⟩ := append_leaf (loc:=loc) F B (after ∅ P) key i s H v lam eta q hB hp.after_subset hv hv1 hlam hp.row hH
  exact (hp.mono_free (Finset.subset_insert _ _)).append_phase hv hv1 hlam _ hh hcount

end MetricKMedianRecovery.RationalLeaves

namespace MetricKMedianRecovery.CanonicalCoupledMerge
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion PhaseMergeRefinement PhaseCountCrossing
  CanonicalMergeCrossing RationalLeaves PhaseMergeInvariant PhaseCoupledMerge
variable {V : Type*} [PseudoMetricSpace V] [DecidableEq V] {d : ℕ}
attribute [local instance] RationalLeaves.metric

def leafState (B : Finset (Label V)) (P : List (List (Label V))) (lam : ℚ)
    (key : ℕ) (i : V) (H : List (Label V)) (l u : ℚ) (T U : List (List (Label V))) : State V :=
  ⟨insert (leaf key i u) B,P++[H++[leaf key i u]],.shorten key i l u,lam,lam,T,U⟩

lemma leaf_certified {loc : Fin d → V} {F : Finset V} {B : Finset (Label V)}
    {v eta lo hi : ℝ} {lam : ℚ} {q n k : ℕ} {P : List (List (Label V))}
    (hp : PrefixData (fun j=>original (loc j)) (F.image original) B v lam eta q P)
    (key : ℕ) (hB : Before key B) (hkey : key<3*(q+1))
    (i : V) (H : List (Label V)) (l u : ℚ) (T U : List (List (Label V)))
    (hv : 0<v) (hv1 : v<1/6) (hlam : (0:ℝ)<lam) (hd : Disjoint (F.image original) B)
    (hl : lo≤(lam:ℝ)) (hu : (lam:ℝ)≤hi)
    (hH : Good (fun j=>original (loc j)) (F.image original) B (after ∅ P) v ((1+v^2)^q) lam eta H)
    (hl0 : 0≤l) (hlu : l≤u) (hw : (u:ℝ)-(l:ℝ)≤eta)
    (hT : Runs (fun j=>original (loc j)) (F.image original) (insert (leaf key i l) B)
      (insert (leaf key i l) (after ∅ P∪H.toFinset)) v lam (q+1) n T)
    (hU : Runs (fun j=>original (loc j)) (F.image original) (insert (leaf key i u) B)
      (insert (leaf key i u) (after ∅ P∪H.toFinset)) v lam (q+1) n U)
    (hs : Sandwich k ((after (insert (leaf key i l) (after ∅ P∪H.toFinset)) T)∩F.image original).card
      ((after (insert (leaf key i u) (after ∅ P∪H.toFinset)) U)∩F.image original).card) :
    Certified loc F v eta lo hi (q+1) n k (leafState B P lam key i H l u T U) := by
  have him := shorten_insert B key hB i l u
  have hpm := prefix_shorten hp key hB i l u H hH.1.1.opened_subset
  have heps : (0:ℝ)≤(u-l:ℚ) := by exact_mod_cast sub_nonneg.mpr hlu
  have heq : ∀ s:ℚ,after ∅ (P++[H++[leaf key i s]])=insert (leaf key i s) (after ∅ P∪H.toFinset) := by
    intro s
    simp only [after_append,after,List.toFinset_append,List.toFinset_cons,List.toFinset_nil,
      Finset.union_empty,Finset.union_insert]
  refine {
    before := (singleton_before key i u B hB).mono (by omega)
    before_map := ?_
    disjoint := ?_
    low := hl
    high := hu
    price := le_rfl
    eps_nonneg := heps
    error := ?_
    inj := shorten_injective key i l u
    fixed := ?_
    shrink := ?_
    loss := ?_
    old_prefix := prefix_leaf hp key hB i u hv hv1 hlam H hH
    new_prefix := ?_
    sandwich := ?_
    new_tail := ?_
    old_tail := ?_ }
  · change Before (3*(q+1)) ((insert (leaf key i u) B).image (shorten key i l u))
    rw [him]
    exact (singleton_before key i l B hB).mono (by omega)
  · change Disjoint (F.image original) (insert (leaf key i u) B)
    rw [Finset.disjoint_insert_right]
    exact ⟨fun he=>fresh F B key hB i u (Finset.mem_union_left _ he),hd⟩
  · change (lam:ℝ)-lam+(d:ℝ)*((1-3*v)*(u-l:ℚ))≤(d:ℝ)*eta
    simp only [sub_self,zero_add]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg d)
    have hh : (0:ℝ)≤(u:ℝ)-(l:ℝ) := by exact_mod_cast sub_nonneg.mpr hlu
    push_cast
    nlinarith only [hv,hh,hw]
  · intro x hx
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hx
    exact shorten_original key i j l u
  · intro j x hx
    exact (shorten_dist key i l u hl0 hlu F B hB (loc j) x hx).1
  · intro j x hx
    exact (shorten_dist key i l u hl0 hlu F B hB (loc j) x hx).2
  · change PrefixData _ _ ((insert (leaf key i u) B).image (shorten key i l u)) _ _ _ _
      ((P++[H++[leaf key i u]]).map (List.map (shorten key i l u)))
    rw [him,hpm]
    exact prefix_leaf hp key hB i l hv hv1 hlam H hH
  · change Sandwich k ((after (after ∅ ((P++[H++[leaf key i u]]).map (List.map (shorten key i l u)))) T)∩F.image original).card
      ((after (after ∅ (P++[H++[leaf key i u]])) U)∩F.image original).card
    simpa only [hpm,heq] using hs
  · change Runs _ _ ((insert (leaf key i u) B).image (shorten key i l u))
      (after ∅ ((P++[H++[leaf key i u]]).map (List.map (shorten key i l u)))) _ _ _ _ T
    simpa only [him,hpm,heq,leafState] using hT
  · change Runs _ _ _ (after ∅ (P++[H++[leaf key i u]])) _ _ _ _ U
    simpa only [heq,leafState] using hU

end MetricKMedianRecovery.CanonicalCoupledMerge

end OAI
