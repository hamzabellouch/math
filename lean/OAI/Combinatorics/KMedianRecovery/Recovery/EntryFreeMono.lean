import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.Mono
import OAI.Combinatorics.KMedianRecovery.Recovery.MaximalSuperset
import OAI.Combinatorics.KMedianRecovery.Geometry.NearestInsertEqual

namespace OAI

namespace MetricKMedianRecovery.PhaseMergeSurgery
open PhaseSequence
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

lemma entry_free_mono {loc : D → X} {F B B' Q : Finset X} {v z lam eta : ℝ} {i : X}
    (h : Entry loc F B Q v z lam eta i) (hB : B ⊆ B') :
    Entry loc F B' Q v z lam eta i := by
  refine ⟨h.1, ?_⟩
  rcases h.2 with hi | ⟨hi,W,hW,hWF,hop⟩
  · exact Or.inl (hB hi)
  · exact Or.inr ⟨hi,W,hW,hWF.trans (Finset.union_subset_union_right hB),hop⟩

lemma prefix_free_mono {loc : D → X} {F B B' Q : Finset X} {v z lam eta : ℝ}
    {H : List X} (h : Prefix loc F B v z lam eta Q H) (hB : B ⊆ B') :
    Prefix loc F B' v z lam eta Q H := by
  induction h with
  | nil Q => exact Prefix.nil Q
  | cons hi ht ih => exact Prefix.cons (entry_free_mono hi hB) ih

lemma prefix_append_iff {loc : D → X} {F B Q : Finset X} {v z lam eta : ℝ}
    {H G : List X} : Prefix loc F B v z lam eta Q (H++G) ↔
      Prefix loc F B v z lam eta Q H ∧
        Prefix loc F B v z lam eta (Q ∪ H.toFinset) G := by
  constructor
  · intro h
    induction H generalizing Q with
    | nil => exact ⟨Prefix.nil Q,by simpa using h⟩
    | cons i H ih =>
      cases h with
      | cons hi ht =>
        obtain ⟨hH,hG⟩ := ih ht
        refine ⟨Prefix.cons hi hH,?_⟩
        simpa only [List.toFinset_cons,Finset.union_insert,Finset.insert_union] using hG
  · rintro ⟨hH,hG⟩
    exact hH.append hG

lemma prefix_exact_eta {loc : D → X} {F B Q : Finset X} {v z lam eta : ℝ}
    {H : List X} (h : Prefix loc F B v z lam 0 Q H) (heta : 0 ≤ eta) :
    Prefix loc F B v z lam eta Q H := by
  induction h with
  | nil Q => exact Prefix.nil Q
  | cons hi ht ih =>
    refine Prefix.cons ⟨hi.1,?_⟩ ih
    rcases hi.2 with hi | ⟨hi,W,hW,hWF,hop⟩
    · exact Or.inl hi
    · exact Or.inr ⟨hi,W,hW,hWF,exact_opening_eta hop heta⟩

theorem append_free (loc : D → X) (F B Q : Finset X) (v z lam eta : ℝ)
    (hv : 0 < v) (hvsmall : v < 1/6) (hz : 0 < z) (hlam : 0 < lam)
    (hrow : ∀ i ∈ F, bidRow loc (1-3*v) z Q i ≤ lam)
    (H : List X) (hH : Valid loc F B Q v z lam eta H)
    (f : X) (hf : f ∉ Q ∪ H.toFinset) :
    Valid loc F (insert f B) Q v z lam eta (H++[f]) := by
  have ht : 0 ≤ 1-3*v := by linarith only [hvsmall]
  refine ⟨(prefix_free_mono hH.1 (Finset.subset_insert _ _)).append
    (Prefix.cons ⟨hf,Or.inl (Finset.mem_insert_self _ _)⟩ (Prefix.nil _)),?_⟩
  apply MaximalPrefixSelection.maximal_superset loc F (Q ∪ H.toFinset)
    (Q ∪ (H++[f]).toFinset) v z lam lam hv hvsmall hz hlam
  · intro i hi
    exact (bidRow_antitone_open loc (1-3*v) z Q (Q ∪ H.toFinset) i ht
      Finset.subset_union_left).trans (hrow i hi)
  · exact hH.2
  · exact le_rfl
  · simp only [List.toFinset_append,List.toFinset_cons,List.toFinset_nil]
    exact Finset.union_subset_union_right Finset.subset_union_left

lemma exact_prefix_avoids_copy (loc : D → X) (F B Q : Finset X) (v z lam : ℝ)
    (i f : X) (hiB : i ∉ B) (hf : f ∈ Q)
    (hco : ∀ j, dist (loc j) i = dist (loc j) f)
    (ht : 0 ≤ 1-3*v) (hlam : 0 < lam) (H : List X)
    (hH : Prefix loc F B v z lam 0 Q H) : i ∉ H := by
  induction hH with
  | nil => simp
  | @cons Q k H hk hH ih =>
    have hki : k ≠ i := by
      intro he
      subst k
      rcases hk.2 with hi | ⟨_,W,hW,_,hop⟩
      · exact hiB hi
      · exact CoincidentCopy.not_openable loc F W (1-3*v) (1+v^2) v z lam 0 i f
          (hW hf) hco ht (by simpa only [mul_zero,sub_zero] using hlam) hop
    simpa only [List.mem_cons,not_or] using
      And.intro (Ne.symm hki) (ih (Finset.mem_insert_of_mem hf))

theorem complete_retaining_copy (loc : D → X) (F B Q : Finset X) (v z lam eta : ℝ)
    (heta : 0 ≤ eta) (hQ : Q ⊆ F ∪ B) (H : List X)
    (hH : Prefix loc F B v z lam eta Q H) (i f : X) (hiB : i ∉ B)
    (hf : f ∈ Q ∪ H.toFinset) (hco : ∀ j, dist (loc j) i = dist (loc j) f)
    (ht : 0 ≤ 1-3*v) (hlam : 0 < lam) :
    ∃ G : List X, (∀ k ∈ G, k ∈ F) ∧ i ∉ G ∧
      Prefix loc F B v z lam 0 (Q ∪ H.toFinset) G ∧
      Valid loc F B Q v z lam eta (H++G) := by
  obtain ⟨G,hG,hreg,hmax⟩ := complete loc F B (Q ∪ H.toFinset) v z lam 0 le_rfl
    (Finset.union_subset hQ hH.opened_subset)
  refine ⟨G,hreg,exact_prefix_avoids_copy loc F B (Q ∪ H.toFinset) v z lam i f
    hiB hf hco ht hlam G hG,hG,hH.append (prefix_exact_eta hG heta),?_⟩
  simpa only [List.toFinset_append,← Finset.union_assoc] using hmax

theorem prefix_replace_open_copy (loc : D → X) (F B Q : Finset X) (v z lam eta : ℝ)
    (i f : X) (hiF : i ∈ F) (hf : f ∈ Q) (hiQ : i ∉ Q)
    (hco : ∀ j, dist (loc j) i = dist (loc j) f)
    (H : List X) (hiH : i ∉ H) (hH : Prefix loc F (insert f B) v z lam eta Q H) :
    Prefix loc F B v z lam eta (insert i (Q.erase f)) H := by
  induction hH with
  | nil => exact Prefix.nil _
  | @cons Q k H hk hH ih =>
    have hki : k ≠ i := by
      intro e
      exact hiH (List.mem_cons.mpr (Or.inl e.symm))
    have hkf : k ≠ f := by
      intro e
      exact hk.1 (e.symm ▸ hf)
    have hin : i ∉ H := fun h => hiH (List.mem_cons_of_mem k h)
    have hiQ' : i ∉ insert k Q := by
      simp only [Finset.mem_insert,not_or]
      exact ⟨Ne.symm hki,hiQ⟩
    apply Prefix.cons
    · refine ⟨?_,?_⟩
      · simp only [Finset.mem_insert,Finset.mem_erase,not_or]
        exact ⟨hki,fun h => hk.1 h.2⟩
      · rcases hk.2 with hb | ⟨hkF,W,hW,hWF,hop⟩
        · exact Or.inl ((Finset.mem_insert.mp hb).resolve_left hkf)
        · have hfW : f ∈ W := hW hf
          refine Or.inr ⟨hkF,insert i (W.erase f),?_,?_,?_⟩
          · exact Finset.insert_subset_insert _ (Finset.erase_subset_erase _ hW)
          · apply Finset.insert_subset (Finset.mem_union_left _ hiF)
            intro x hx
            obtain ⟨hxf,hxW⟩ := Finset.mem_erase.mp hx
            rcases Finset.mem_union.mp (hWF hxW) with hxF | hxB
            · exact Finset.mem_union_left _ hxF
            · exact Finset.mem_union_right _ ((Finset.mem_insert.mp hxB).resolve_left hxf)
          · have he : insert f (W.erase f) = W := Finset.insert_erase hfW
            rw [← he] at hop
            exact (CoincidentCopy.openable_insert_equal loc F (W.erase f) (1-3*v)
              (1+v^2) v z lam eta f i k (fun j => (hco j).symm)).mp hop
    · have hh := ih (Finset.mem_insert_of_mem hf) hiQ' hin
      simpa only [Finset.erase_insert_of_ne hkf,Finset.insert_comm] using hh

theorem regularize (loc : D → X) (F B Q : Finset X) (v z lam eta : ℝ)
    (C G : List X) (i f : X) (hiF : i ∈ F) (hfF : f ∉ F)
    (hfQ : f ∉ Q ∪ C.toFinset) (hiG : i ∉ G)
    (hco : ∀ j, dist (loc j) i = dist (loc j) f)
    (hC : Prefix loc F B v z lam eta Q C)
    (hi : Entry loc F B (Q ∪ C.toFinset) v z lam eta i)
    (hold : Valid loc F (insert f B) Q v z lam eta (C++f::G)) :
    Valid loc F B Q v z lam eta (C++i::G) := by
  have hs := (prefix_append_iff.mp hold.1).2
  cases hs with
  | cons hfree hG =>
    have hiQ : i ∉ insert f (Q ∪ C.toFinset) := by
      simp only [Finset.mem_insert,not_or]
      exact ⟨fun he => hfF (he ▸ hiF),hi.1⟩
    have hnew := prefix_replace_open_copy loc F B (insert f (Q ∪ C.toFinset))
      v z lam eta i f hiF (Finset.mem_insert_self _ _) hiQ hco G hiG hG
    have hnew' : Prefix loc F B v z lam eta (insert i (Q ∪ C.toFinset)) G := by
      simpa only [Finset.erase_insert hfQ] using hnew
    refine ⟨hC.append (Prefix.cons hi hnew'),?_⟩
    have hmax : Maximal loc F (insert f (Q ∪ C.toFinset ∪ G.toFinset)) v z lam := by
      simpa only [List.toFinset_append,List.toFinset_cons,Finset.union_insert,
        Finset.insert_union,Finset.union_assoc] using hold.2
    have hm : Maximal loc F (insert i (Q ∪ C.toFinset ∪ G.toFinset)) v z lam := by
      intro k hk hkn hop
      have hkf : k ≠ f := fun he => hfF (he ▸ hk)
      have hkQ : k ∉ Q ∪ C.toFinset ∪ G.toFinset :=
        fun hh => hkn (Finset.mem_insert_of_mem hh)
      exact hmax k hk (by simpa only [Finset.mem_insert,not_or] using And.intro hkf hkQ)
        ((CoincidentCopy.openable_insert_equal loc F (Q ∪ C.toFinset ∪ G.toFinset)
          (1-3*v) (1+v^2) v z lam 0 f i k (fun j => (hco j).symm)).mpr hop)
    simpa only [List.toFinset_append,List.toFinset_cons,Finset.union_insert,
      Finset.insert_union,Finset.union_assoc] using hm

theorem delete_suffix_with_copy (loc : D → X) (F B Q : Finset X) (v z lam eta : ℝ)
    (hv : 0 < v) (hvsmall : v < 1/6) (hz : 0 < z) (hlam : 0 < lam)
    (hrow : ∀ k ∈ F, bidRow loc (1-3*v) z Q k ≤ lam)
    (C T G R : List X) (i f : X) (hf : f ∉ Q ∪ (C++T++G).toFinset)
    (hco : ∀ j, dist (loc j) i = dist (loc j) f)
    (hbefore : Valid loc F B Q v z lam eta (C++i::T))
    (hafter : Prefix loc F B v z lam eta Q (C++T++G))
    (hRG : R.Sublist G) :
    Valid loc F (insert f B) Q v z lam eta ((C++T++R)++[f]) := by
  have ht : 0 ≤ 1-3*v := by linarith only [hvsmall]
  have hsub : (C++T++R).Sublist (C++T++G) := hRG.append_left (C++T)
  have hp := prefix_free_mono (hafter.sublist hsub) (Finset.subset_insert f B)
  have hf' : f ∉ Q ∪ (C++T++R).toFinset := by
    intro hm
    apply hf
    rcases Finset.mem_union.mp hm with h | h
    · exact Finset.mem_union_left _ h
    · exact Finset.mem_union_right _
        (List.mem_toFinset.mpr (hsub.subset (List.mem_toFinset.mp h)))
  refine ⟨hp.append (Prefix.cons ⟨hf',Or.inl (Finset.mem_insert_self _ _)⟩ (Prefix.nil _)),?_⟩
  have hmax : Maximal loc F (insert i (Q ∪ C.toFinset ∪ T.toFinset)) v z lam := by
    simpa only [List.toFinset_append,List.toFinset_cons,Finset.union_insert,
      Finset.insert_union,Finset.union_assoc] using hbefore.2
  have hmax' := CoincidentCopy.maximal_replace loc F (Q ∪ C.toFinset ∪ T.toFinset)
    v z lam i f hco ht hlam hmax
  apply MaximalPrefixSelection.maximal_superset loc F
    (insert f (Q ∪ C.toFinset ∪ T.toFinset)) _ v z lam lam hv hvsmall hz hlam
  · intro k hk
    exact (bidRow_antitone_open loc (1-3*v) z Q _ k ht
      (fun x hx => Finset.mem_insert_of_mem
        (Finset.mem_union_left _ (Finset.mem_union_left _ hx)))).trans (hrow k hk)
  · exact hmax'
  · exact le_rfl
  · intro x hx
    simp only [List.toFinset_append,List.toFinset_cons,List.toFinset_nil,
      Finset.mem_union,Finset.mem_insert,Finset.notMem_empty,or_false] at hx ⊢
    tauto

end MetricKMedianRecovery.PhaseMergeSurgery

end OAI
