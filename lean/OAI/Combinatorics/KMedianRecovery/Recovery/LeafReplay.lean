import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.MergeCross
import OAI.Combinatorics.KMedianRecovery.Geometry.NearestImage
import OAI.Combinatorics.KMedianRecovery.Geometry.NearestMap
import OAI.Combinatorics.KMedianRecovery.Algorithms.BudgetBound
import OAI.Combinatorics.KMedianRecovery.Encoding.RationalLeaves

namespace OAI

namespace MetricKMedianRecovery.CanonicalLeafReplay
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion CanonicalMergeCrossing
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

lemma Runs.swap_free {loc : D → X} {F B Q : Finset X} {v lam : ℝ} {q n : ℕ}
    {T : List (List X)} (h : Runs loc F B Q v lam q n T) (i f : X)
    (hi : i∉F) (hf : f∉F∪B) (hd : ∀ j,dist (loc j) i=dist (loc j) f)
    (ht : 0≤1-3*v) (hlam : 0<lam) :
    Runs loc F (insert f B) (Q.image (Equiv.swap i f)) v lam q n T ∧
      ((after Q T)∩F).card=((after (Q.image (Equiv.swap i f)) T)∩F).card := by
  have hfix : ∀ x∈F,Equiv.swap i f x=x := by
    intro x hx
    exact Equiv.swap_apply_of_ne_of_ne (fun he=>hi (he ▸ hx))
      (fun he=>hf (Finset.mem_union_left _ (he ▸ hx)))
  have hT : T.map (List.map (Equiv.swap i f))=T := by
    have hmap : ∀ H∈T,H.map (Equiv.swap i f)=H := by
      intro H hH
      calc
        _=H.map id := List.map_congr_left (fun x hx=>hfix x (h.2.2 H hH x hx))
        _=H := List.map_id H
    calc
      _=T.map id := List.map_congr_left hmap
      _=T := List.map_id T
  have hF : F.image (Equiv.swap i f)=F := by
    calc
      _=F.image id := Finset.image_congr hfix
      _=F := Finset.image_id
  refine ⟨⟨h.1,?_,h.2.2⟩,?_⟩
  · simpa only [hT] using CoincidentHistory.history_swap loc F B Q v lam 0 i f hf hd ht hlam q T h.2.1
  · conv_rhs => rw [←hT,HistoryIsometry.after_map,←hF,
      ←Finset.image_inter _ _ (Equiv.swap i f).injective,
      Finset.card_image_of_injective _ (Equiv.swap i f).injective]

lemma Runs.insert_far {loc : D → X} {F B Q : Finset X} {v lam : ℝ} {q n : ℕ}
    {T : List (List X)} (h : Runs loc F B Q v lam q n T) (M : ℝ) (f : X)
    (hF : F.Nonempty) (hv : 0<v) (hv1 : v<1/6) (hlam : 0<lam) (hM : 0≤M)
    (hf : f∉F∪B) (hdiam : ∀ i∈F,∀ j,dist i (loc j)≤M)
    (hfar : ∀ j,(1+v^2)*(M+lam)<(1-3*v)*dist (loc j) f)
    (hrow : ∀ i∈F,bidRow loc (1-3*v) ((1+v^2)^q) Q i≤lam) :
    Runs loc F (insert f B) (insert f Q) v lam q n T ∧
      ((after Q T)∩F).card=((after (insert f Q) T)∩F).card := by
  refine ⟨⟨h.1,UniformRowDisabling.history_insert loc F B Q hF v lam 0 M f q T
    hv hv1 hlam hM hf hdiam hfar hrow h.2.1,h.2.2⟩,?_⟩
  rw [DisablingHistory.after_insert,Finset.insert_inter_of_notMem
    (fun he=>hf (Finset.mem_union_left _ he))]

lemma Runs.replace_paid {loc : D → X} {F B R : Finset X} {v lam : ℝ} {q n : ℕ}
    {T : List (List X)} (i f : X) (hi : i∈F) (hf : f∈B) (hdis : Disjoint F B)
    (hiR : i∉R) (hfR : f∉R) (hd : ∀ j,dist (loc j) i=dist (loc j) f)
    (ht : 0≤1-3*v) (hlam : 0<lam) (h : Runs loc F B (insert i R) v lam q n T) :
    Runs loc F B (insert f R) v lam q n T ∧
      ((after (insert i R) T)∩F).card=((after (insert f R) T)∩F).card+1 := by
  obtain ⟨hh,U,hiU,_,ha,hb⟩ := history_twin loc F B v lam i f hi hf hdis hd ht hlam
    T q R hiR hfR h.2.2 h.2.1
  refine ⟨⟨h.1,hh,h.2.2⟩,?_⟩
  rw [ha,hb,Finset.inter_comm (insert i U),Finset.inter_comm (insert f U)]
  exact CoincidentCopy.paid_count F U i f hi hiU (fun he=>Finset.disjoint_left.mp hdis he hf)

end MetricKMedianRecovery.CanonicalLeafReplay

namespace MetricKMedianRecovery.RationalLeaves

section
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion CanonicalMergeCrossing CanonicalLeafReplay
variable {V : Type*} [PseudoMetricSpace V] [DecidableEq V] {d : ℕ}
attribute [local instance] metric

lemma far_replay (loc : Fin d → V) (F : Finset V) (B Q : Finset (Label V))
    (key : ℕ) (i : V) (v lam M : ℝ) (q n N : ℕ) (s : ℚ) (T : List (List (Label V)))
    (hF : F.Nonempty) (hB : Before key B) (hv : 0<v) (hv1 : v<1/6) (hlam : 0<lam)
    (hM : 0<M) (hN : 3≤N) (hlamUpper : lam≤8*N*M) (hs : 20*N*M≤(s:ℝ))
    (hdiam : ∀ i∈F,∀ j,dist i (loc j)≤M)
    (hrow : ∀ x∈F.image original,bidRow (fun j=>original (loc j)) (1-3*v) ((1+v^2)^q) Q x≤lam)
    (h : Runs (fun j=>original (loc j)) (F.image original) B Q v lam q n T) :
    Runs (fun j=>original (loc j)) (F.image original) (insert (leaf key i s) B)
      (insert (leaf key i s) Q) v lam q n T ∧
      ((after Q T)∩F.image original).card=((after (insert (leaf key i s) Q) T)∩F.image original).card := by
  apply Runs.insert_far h M (leaf key i s) (hF.image original) hv hv1 hlam hM.le (fresh F B key hB i s)
  · rintro x hx j
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
    simpa only [original_dist] using hdiam a ha j
  · intro j
    obtain ⟨h₁,h₂⟩ := DisablingCopy.numerical_bound v M N hv hv1 hM hN
    have h₀ : (1+v^2)*(M+lam)≤(1+v^2)*(M+8*N*M) :=
      mul_le_mul_of_nonneg_left (by linarith only [hlamUpper]) (by positivity)
    have ht : 0≤1-3*v := by linarith only [hv1]
    have hs' : 20*N*M≤dist (original (loc j)) (leaf key i s) := by
      rw [leaf_dist]
      have hm : (s:ℝ)≤(max s 0:ℚ) := by exact_mod_cast le_max_left s 0
      exact hs.trans (hm.trans (le_add_of_nonneg_left dist_nonneg))
    exact (h₀.trans_lt (h₁.trans h₂)).trans_le (mul_le_mul_of_nonneg_left hs' ht)
  · exact hrow

end

open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion CanonicalMergeCrossing CanonicalLeafReplay
variable {V : Type*} [PseudoMetricSpace V] [DecidableEq V] {d : ℕ}
attribute [local instance] metric

lemma zero_free_replay (loc : Fin d → V) (F : Finset V) (B Q : Finset (Label V))
    (key : ℕ) (i : V) (f : Label V) (H : List (Label V)) (T : List (List (Label V)))
    (v lam eta : ℝ) (q n : ℕ) (hB : Before key B) (hdis : Disjoint (F.image original) B)
    (hQ : Q⊆F.image original ∪ B) (hf : f∈B) (hd : ∀ j,dist (original (loc j)) (original i)=dist (original (loc j)) f)
    (ht : 0≤1-3*v) (hlam : 0<lam)
    (hphase : Valid (fun j=>original (loc j)) (F.image original) B Q v ((1+v^2)^q) lam eta (H++[f]))
    (h : Runs (fun j=>original (loc j)) (F.image original) B (Q∪(H++[f]).toFinset) v lam (q+1) n T) :
    Runs (fun j=>original (loc j)) (F.image original) (insert (leaf key i 0) B)
      (insert (leaf key i 0) (Q∪H.toFinset)) v lam (q+1) n T ∧
      finalCount (F.image original) Q (H++[f]) T =
        ((after (insert (leaf key i 0) (Q∪H.toFinset)) T)∩F.image original).card := by
  have hfF : f∉F.image original := fun he=>Finset.disjoint_left.mp hdis he hf
  have hfQ : f∉Q∪H.toFinset := by
    have he := PhaseMergeRefinement.entry_fresh (C:=H) (T:=[]) hphase.1
    simpa only [List.append_nil] using he
  have hfresh := fresh F B key hB i 0
  have hco : ∀ j,dist (original (loc j)) f=dist (original (loc j)) (leaf key i 0) := by
    intro j
    rw [←hd j,leaf_dist,original_dist]
    simp
  obtain ⟨hh,hcount⟩ := Runs.swap_free h f (leaf key i 0) hfF hfresh hco ht hlam
  have hsub : Q∪H.toFinset⊆F.image original ∪ B := by
    apply Finset.union_subset hQ
    intro x hx
    apply hphase.1.opened_subset
    exact List.mem_toFinset.mpr (List.mem_append_left _ (List.mem_toFinset.mp hx))
  have hfix : ∀ x∈Q∪H.toFinset,Equiv.swap f (leaf key i 0) x=x := by
    intro x hx
    apply Equiv.swap_apply_of_ne_of_ne
    · intro he; exact hfQ (he ▸ hx)
    · intro he; exact hfresh (hsub (he ▸ hx))
  have him : (Q∪H.toFinset).image (Equiv.swap f (leaf key i 0))=Q∪H.toFinset := by
    calc
      _=(Q∪H.toFinset).image id := Finset.image_congr hfix
      _=_ := Finset.image_id
  have hb : Q∪(H++[f]).toFinset=insert f (Q∪H.toFinset) := by
    simp only [List.toFinset_append,List.toFinset_cons,List.toFinset_nil,Finset.union_insert,Finset.union_empty]
  simpa only [finalCount,hb,Finset.image_insert,Equiv.swap_apply_left,him] using And.intro hh hcount

lemma zero_paid_replay (loc : Fin d → V) (F : Finset V) (B Q : Finset (Label V))
    (key : ℕ) (i : V) (C H : List (Label V)) (T : List (List (Label V)))
    (v lam eta : ℝ) (q n : ℕ) (hi : i∈F) (hB : Before key B)
    (hdis : Disjoint (F.image original) B) (hQ : Q⊆F.image original ∪ B)
    (ht : 0≤1-3*v) (hlam : 0<lam)
    (hphase : Valid (fun j=>original (loc j)) (F.image original) B Q v ((1+v^2)^q) lam eta (C++original i::H))
    (h : Runs (fun j=>original (loc j)) (F.image original) B (Q∪(C++original i::H).toFinset) v lam (q+1) n T) :
    Runs (fun j=>original (loc j)) (F.image original) (insert (leaf key i 0) B)
      (insert (leaf key i 0) (Q∪(C++H).toFinset)) v lam (q+1) n T ∧
      finalCount (F.image original) Q (C++original i::H) T =
        ((after (insert (leaf key i 0) (Q∪(C++H).toFinset)) T)∩F.image original).card+1 := by
  have hfresh := fresh F B key hB i 0
  have hiQ := PhaseMergeRefinement.entry_fresh hphase.1
  have hco : ∀ j,dist (original (loc j)) (original i)=dist (original (loc j)) (leaf key i 0) := by
    intro j; rw [leaf_dist,original_dist]; simp
  have hd' : Disjoint (F.image original) (insert (leaf key i 0) B) := by
    rw [Finset.disjoint_insert_right]
    exact ⟨fun he=>hfresh (Finset.mem_union_left _ he),hdis⟩
  have hb : Q∪(C++original i::H).toFinset=insert (original i) (Q∪(C++H).toFinset) := by
    simp only [List.toFinset_append,List.toFinset_cons,Finset.union_insert]
  have hfR : leaf key i 0∉Q∪(C++H).toFinset := by
    intro he
    apply hfresh
    rcases Finset.mem_union.mp he with he|he
    · exact hQ he
    · apply hphase.1.opened_subset
      apply List.mem_toFinset.mpr
      rcases List.mem_append.mp (List.mem_toFinset.mp he) with he|he
      · exact List.mem_append_left _ he
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ he)
  have hm := h.mono_free (Finset.subset_insert (leaf key i 0) B)
  rw [hb] at hm
  obtain ⟨hh,hcount⟩ := Runs.replace_paid (original i) (leaf key i 0)
    (Finset.mem_image.mpr ⟨i,hi,rfl⟩) (Finset.mem_insert_self _ _) hd' hiQ hfR hco ht hlam hm
  exact ⟨hh,by simpa only [finalCount,hb] using hcount⟩

lemma append_leaf (loc : Fin d → V) (F : Finset V) (B Q : Finset (Label V))
    (key : ℕ) (i : V) (s : ℚ) (H : List (Label V)) (v lam eta : ℝ) (q : ℕ)
    (hB : Before key B) (hQ : Q⊆F.image original∪B)
    (hv : 0<v) (hv1 : v<1/6) (hlam : 0<lam)
    (hrow : ∀ x∈F.image original,bidRow (fun j=>original (loc j)) (1-3*v) ((1+v^2)^q) Q x≤lam)
    (hH : PhaseMergeRefinement.Good (fun j=>original (loc j)) (F.image original) B Q v ((1+v^2)^q) lam eta H) :
    Valid (fun j=>original (loc j)) (F.image original) (insert (leaf key i s) B) Q v ((1+v^2)^q) lam eta (H++[leaf key i s]) ∧
      ((H++[leaf key i s]).toFinset \ F.image original).card≤3 := by
  have hfresh := fresh F B key hB i s
  have hf : leaf key i s∉Q∪H.toFinset := fun he=>hfresh ((Finset.union_subset hQ hH.1.1.opened_subset) he)
  refine ⟨PhaseMergeSurgery.append_free _ _ _ _ _ _ _ _ hv hv1 (by positivity) hlam hrow H hH.1 _ hf,?_⟩
  have hfF : leaf key i s∉F.image original := fun he=>hfresh (Finset.mem_union_left _ he)
  have hfH : leaf key i s∉H.toFinset := fun he=>hf (Finset.mem_union_right _ he)
  simp only [List.toFinset_append,List.toFinset_cons,List.toFinset_nil,Finset.union_insert,Finset.union_empty]
  rw [Finset.insert_sdiff_of_notMem _ hfF,Finset.card_insert_of_notMem
    (fun he=>hfH (Finset.mem_sdiff.mp he).1)]
  have hh := hH.2
  omega

end MetricKMedianRecovery.RationalLeaves

end OAI
