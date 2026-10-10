import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.EntryFreeMono

namespace OAI

namespace MetricKMedianRecovery.PhaseMergePath
open PhaseSequence PhaseMergeSurgery
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

def pool (F B : Finset X) (copy : X → X) : Finset X := B ∪ F.image copy

omit [PseudoMetricSpace X] in
lemma subset_pool (F B : Finset X) (copy : X → X) : B ⊆ pool F B copy :=
  Finset.subset_union_left

omit [PseudoMetricSpace X] in
lemma insert_subset_pool {F B : Finset X} {copy : X → X} {i : X} (hi : i ∈ F) :
    insert (copy i) B ⊆ pool F B copy :=
  Finset.insert_subset (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i,hi,rfl⟩))
    (subset_pool F B copy)

def Good (loc : D → X) (F B Q : Finset X) (copy : X → X) (v z lam eta : ℝ)
    (H : List X) : Prop :=
  Valid loc F (pool F B copy) Q v z lam eta H ∧ (H.toFinset \ F).card ≤ 1

inductive Step (loc : D → X) (F B Q : Finset X) (copy : X → X) (v z lam : ℝ) :
    List X → List X → Prop
  | add (H : List X) (i : X) (hi : i ∈ F) : Step loc F B Q copy v z lam H (H++[copy i])
  | remove (C T A : List X) (i : X) (hi : i ∈ F)
      (hA : Prefix loc F (pool F B copy) v z lam 0 (Q ∪ (C++T).toFinset) A)
      (hreg : ∀ x ∈ A, x ∈ F) :
      Step loc F B Q copy v z lam (C++i::T) ((C++T)++A)
  | replace (C T : List X) (i : X) (hi : i ∈ F)
      (hnot : i ∉ Q ∪ (C++T).toFinset) :
      Step loc F B Q copy v z lam (C++copy i::T) (C++i::T)

inductive Walk (loc : D → X) (F B Q : Finset X) (copy : X → X) (v z lam eta : ℝ) :
    ℕ → List X → List X → Prop
  | nil {H} (hgood : Good loc F B Q copy v z lam eta H) :
      Walk loc F B Q copy v z lam eta 0 H H
  | cons {n H G J} (hgood : Good loc F B Q copy v z lam eta H)
      (hstep : Step loc F B Q copy v z lam H G)
      (tail : Walk loc F B Q copy v z lam eta n G J) :
      Walk loc F B Q copy v z lam eta (n+1) H J

lemma Walk.trans {loc : D → X} {F B Q : Finset X} {copy : X → X} {v z lam eta : ℝ}
    {n m : ℕ} {H G J : List X} (h : Walk loc F B Q copy v z lam eta n H G)
    (g : Walk loc F B Q copy v z lam eta m G J) :
    Walk loc F B Q copy v z lam eta (n+m) H J := by
  induction h with
  | nil => simpa using g
  | cons hh hs ht ih => simpa only [Nat.add_right_comm] using Walk.cons hh hs (ih g)

lemma Walk.first_good {loc : D → X} {F B Q : Finset X} {copy : X → X} {v z lam eta : ℝ}
    {n : ℕ} {H G : List X} (h : Walk loc F B Q copy v z lam eta n H G) :
    Good loc F B Q copy v z lam eta H := by
  cases h with
  | nil h => exact h
  | cons h _ _ => exact h

lemma Walk.last_good {loc : D → X} {F B Q : Finset X} {copy : X → X} {v z lam eta : ℝ}
    {n : ℕ} {H G : List X} (h : Walk loc F B Q copy v z lam eta n H G) :
    Good loc F B Q copy v z lam eta G := by
  induction h with
  | nil h => exact h
  | cons _ _ _ ih => exact ih

lemma regular_good {loc : D → X} {F B Q : Finset X} {copy : X → X} {v z lam eta : ℝ}
    {H : List X} (hH : Valid loc F B Q v z lam eta H) (hreg : ∀ k ∈ H, k ∈ F) :
    Good loc F B Q copy v z lam eta H := by
  refine ⟨⟨prefix_free_mono hH.1 (subset_pool F B copy),hH.2⟩,?_⟩
  have hs : H.toFinset ⊆ F := fun k hk => hreg k (List.mem_toFinset.mp hk)
  simp only [Finset.sdiff_eq_empty_iff_subset.mpr hs,Finset.card_empty,Nat.zero_le]

lemma one_copy_good {loc : D → X} {F B Q : Finset X} {copy : X → X} {v z lam eta : ℝ}
    {H : List X} {i : X} (hi : i ∈ F)
    (hH : Valid loc F (insert (copy i) B) Q v z lam eta H)
    (hreg : ∀ k ∈ H, k ∈ F ∨ k = copy i) :
    Good loc F B Q copy v z lam eta H := by
  refine ⟨⟨prefix_free_mono hH.1 (insert_subset_pool hi),hH.2⟩,?_⟩
  have hs : H.toFinset \ F ⊆ {copy i} := by
    intro k hk
    obtain ⟨hkH,hkF⟩ := Finset.mem_sdiff.mp hk
    exact Finset.mem_singleton.mpr ((hreg k (List.mem_toFinset.mp hkH)).resolve_left hkF)
  exact (Finset.card_le_card hs).trans (by simp)

theorem delete_old_suffix (loc : D → X) (F B Q : Finset X) (copy : X → X)
    (v z lam eta : ℝ) (heta : 0 ≤ eta) (hQ : Q ⊆ F ∪ B)
    (ht : 0 ≤ 1-3*v) (hlam : 0 < lam) (C U E : List X) (i : X)
    (hiF : i ∈ F) (hiB : i ∉ B) (hif : i ≠ copy i)
    (hco : ∀ j, dist (loc j) i = dist (loc j) (copy i))
    (hC : ∀ k ∈ C, k ∈ F) (hU : ∀ k ∈ U, k ∈ F) (hE : ∀ k ∈ E, k ∈ F)
    (hiE : i ∉ E)
    (hvalid : Valid loc F (insert (copy i) B) Q v z lam eta (C++U++copy i::E)) :
    ∃ G : List X, ∃ n : ℕ, n ≤ U.length ∧ (∀ k ∈ G, k ∈ F) ∧ i ∉ G ∧
      Valid loc F (insert (copy i) B) Q v z lam eta (C++copy i::G) ∧
      Walk loc F B Q copy v z lam eta n (C++U++copy i::E) (C++copy i::G) := by
  induction U generalizing E with
  | nil =>
    have hv' : Valid loc F (insert (copy i) B) Q v z lam eta (C++copy i::E) := by
      simpa only [List.append_nil] using hvalid
    refine ⟨E,0,by simp,hE,hiE,hv',?_⟩
    simp only [List.append_nil]
    apply Walk.nil
    apply one_copy_good hiF hv'
    intro k hk
    rcases List.mem_append.mp hk with hk | hk
    · exact Or.inl (hC k hk)
    · rcases List.mem_cons.mp hk with rfl | hk
      · exact Or.inr rfl
      · exact Or.inl (hE k hk)
  | cons u U ih =>
    have huF : u ∈ F := hU u (List.mem_cons_self ..)
    have hUr : ∀ k ∈ U, k ∈ F := fun k hk => hU k (List.mem_cons_of_mem _ hk)
    have hsub : (C++U++copy i::E).Sublist (C++(u::U)++copy i::E) := by
      simpa only [List.append_assoc,List.cons_append] using
        (List.Sublist.cons u (List.Sublist.refl (U++copy i::E))).append_left C
    have hret := hvalid.1.sublist hsub
    have hf : copy i ∈ Q ∪ (C++U++copy i::E).toFinset := by simp
    have hiB' : i ∉ insert (copy i) B := by simpa only [Finset.mem_insert,not_or] using ⟨hif,hiB⟩
    have hQ' : Q ⊆ F ∪ insert (copy i) B :=
      hQ.trans (Finset.union_subset_union_right (Finset.subset_insert _ _))
    obtain ⟨A,hAreg,hiA,hA,hvA⟩ := complete_retaining_copy loc F (insert (copy i) B) Q
      v z lam eta heta hQ' (C++U++copy i::E) hret i (copy i) hiB' hf hco ht hlam
    have hEA : ∀ k ∈ E++A, k ∈ F := by
      intro k hk
      exact (List.mem_append.mp hk).elim (hE k) (hAreg k)
    have hiEA : i ∉ E++A := by simpa only [List.mem_append,not_or] using ⟨hiE,hiA⟩
    have hvEA : Valid loc F (insert (copy i) B) Q v z lam eta (C++U++copy i::(E++A)) := by
      simpa only [List.append_assoc,List.cons_append] using hvA
    obtain ⟨G,n,hn,hG,hiG,hvG,hw⟩ := ih (E++A) hUr hEA hiEA hvEA
    refine ⟨G,n+1,by simpa only [List.length_cons] using Nat.add_le_add_right hn 1,
      hG,hiG,hvG,?_⟩
    have hg : Good loc F B Q copy v z lam eta (C++(u::U)++copy i::E) := by
      apply one_copy_good hiF hvalid
      intro k hk
      simp only [List.mem_append,List.mem_cons] at hk
      rcases hk with (hk | hk) | hk | hk
      · exact Or.inl (hC k hk)
      · exact Or.inl (hU k (List.mem_cons.mpr hk))
      · exact Or.inr hk
      · exact Or.inl (hE k hk)
    have hs := Step.remove (loc := loc) (F := F) (B := B) (Q := Q) (copy := copy)
      (v := v) (z := z) (lam := lam) C (U++copy i::E) A u huF
      (by simpa only [List.append_assoc] using prefix_free_mono hA (insert_subset_pool hiF)) hAreg
    apply Walk.cons hg
    · simpa only [List.append_assoc,List.cons_append] using hs
    · simpa only [List.append_assoc,List.cons_append] using hw

lemma regular_length {loc : D → X} {F B Q : Finset X} {v z lam eta : ℝ} {H : List X}
    (hH : Prefix loc F B v z lam eta Q H) (hreg : ∀ k ∈ H, k ∈ F) : H.length ≤ F.card := by
  rw [← List.toFinset_card_of_nodup hH.nodup]
  exact Finset.card_le_card (fun k hk => hreg k (List.mem_toFinset.mp hk))

theorem advance_prefix (loc : D → X) (F B Q : Finset X) (copy : X → X)
    (v z lam eta : ℝ) (hv : 0 < v) (hvsmall : v < 1/6) (hz : 0 < z)
    (hlam : 0 < lam) (heta : 0 ≤ eta) (hQ : Q ⊆ F ∪ B)
    (hrow : ∀ k ∈ F, bidRow loc (1-3*v) z Q k ≤ lam)
    (C U : List X) (i : X) (hiF : i ∈ F) (hiB : i ∉ B)
    (hfresh : copy i ∉ F ∪ B) (hco : ∀ j, dist (loc j) i = dist (loc j) (copy i))
    (hC : Prefix loc F B v z lam eta Q C)
    (hi : Entry loc F B (Q ∪ C.toFinset) v z lam eta i)
    (hCr : ∀ k ∈ C, k ∈ F) (hUr : ∀ k ∈ U, k ∈ F)
    (hcur : Valid loc F B Q v z lam eta (C++U)) :
    ∃ G : List X, ∃ n : ℕ, n ≤ U.length+2 ∧ (∀ k ∈ G, k ∈ F) ∧
      Valid loc F B Q v z lam eta (C++i::G) ∧
      Walk loc F B Q copy v z lam eta n (C++U) (C++i::G) := by
  have ht : 0 ≤ 1-3*v := by linarith only [hvsmall]
  have hfF : copy i ∉ F := fun hf => hfresh (Finset.mem_union_left _ hf)
  have hir : i ≠ copy i := fun he => hfF (he ▸ hiF)
  have hr : ∀ k ∈ C++U, k ∈ F := by
    intro k hk
    exact (List.mem_append.mp hk).elim (hCr k) (hUr k)
  have hf : copy i ∉ Q ∪ (C++U).toFinset := by
    intro hm
    rcases Finset.mem_union.mp hm with hm | hm
    · exact hfresh (hQ hm)
    · exact hfF (hr _ (List.mem_toFinset.mp hm))
  have happ := append_free loc F B Q v z lam eta hv hvsmall hz hlam hrow (C++U) hcur (copy i) hf
  obtain ⟨G,n,hn,hGr,hiG,hvalid,hw⟩ := delete_old_suffix loc F B Q copy v z lam eta
    heta hQ ht hlam C U [] i hiF hiB hir hco hCr hUr (by simp) (by simp) happ
  have hfC : copy i ∉ Q ∪ C.toFinset := by
    intro hm
    apply hf
    rcases Finset.mem_union.mp hm with hm | hm
    · exact Finset.mem_union_left _ hm
    · exact Finset.mem_union_right _ (by simpa only [List.toFinset_append] using Finset.mem_union_left U.toFinset hm)
  have hvG := regularize loc F B Q v z lam eta C G i (copy i) hiF hfF hfC hiG hco hC hi hvalid
  have hCG : ∀ k ∈ C++i::G, k ∈ F := by
    intro k hk
    rcases List.mem_append.mp hk with hk | hk
    · exact hCr k hk
    · rcases List.mem_cons.mp hk with rfl | hk
      · exact hiF
      · exact hGr k hk
  have hi' : i ∉ Q ∪ (C++G).toFinset := by
    simp only [List.toFinset_append,Finset.mem_union,not_or,List.mem_toFinset]
    exact ⟨fun h => hi.1 (Finset.mem_union_left _ h),
      fun h => hi.1 (Finset.mem_union_right _ (List.mem_toFinset.mpr h)),hiG⟩
  have hs := Step.replace (loc := loc) (B := B) (copy := copy) (v := v) (z := z)
    (lam := lam) C G i hiF hi'
  have hw' := hw.trans (Walk.cons hw.last_good hs (Walk.nil (regular_good hvG hCG)))
  have hw'' := Walk.cons (regular_good hcur hr) (Step.add _ i hiF) hw'
  refine ⟨G,n+2,by omega,hGr,hvG,?_⟩
  simpa only [Nat.add_zero,Nat.add_assoc] using hw''

theorem match_prefix (loc : D → X) (F B Q : Finset X) (copy : X → X)
    (v z lam eta : ℝ) (hv : 0 < v) (hvsmall : v < 1/6) (hz : 0 < z)
    (hlam : 0 < lam) (heta : 0 ≤ eta) (hQ : Q ⊆ F ∪ B) (hdis : Disjoint F B)
    (hrow : ∀ k ∈ F, bidRow loc (1-3*v) z Q k ≤ lam)
    (hfresh : ∀ i ∈ F, copy i ∉ F ∪ B)
    (hco : ∀ i ∈ F, ∀ j, dist (loc j) i = dist (loc j) (copy i))
    (C U T : List X) (hCr : ∀ k ∈ C, k ∈ F) (hUr : ∀ k ∈ U, k ∈ F)
    (hTr : ∀ k ∈ T, k ∈ F)
    (htarget : Prefix loc F B v z lam eta Q (C++T))
    (hcur : Valid loc F B Q v z lam eta (C++U)) :
    ∃ G : List X, ∃ n : ℕ, n ≤ T.length*(F.card+2) ∧ (∀ k ∈ G, k ∈ F) ∧
      Valid loc F B Q v z lam eta (C++T++G) ∧
      Walk loc F B Q copy v z lam eta n (C++U) (C++T++G) := by
  induction T generalizing C U with
  | nil =>
    refine ⟨U,0,by simp,hUr,by simpa using hcur,?_⟩
    simp only [List.append_nil]
    apply Walk.nil
    apply regular_good hcur
    intro k hk
    exact (List.mem_append.mp hk).elim (hCr k) (hUr k)
  | cons i T ih =>
    have hiF : i ∈ F := hTr i (List.mem_cons_self ..)
    have hiB : i ∉ B := fun hi => Finset.disjoint_left.mp hdis hiF hi
    have hTr' : ∀ k ∈ T, k ∈ F := fun k hk => hTr k (List.mem_cons_of_mem _ hk)
    obtain ⟨hC,hIT⟩ := prefix_append_iff.mp htarget
    cases hIT with
    | cons hi hT =>
      obtain ⟨G,n,hn,hGr,hvG,hw⟩ := advance_prefix loc F B Q copy v z lam eta
        hv hvsmall hz hlam heta hQ hrow C U i hiF hiB (hfresh i hiF) (hco i hiF)
        hC hi hCr hUr hcur
      have hCi : ∀ k ∈ C++[i], k ∈ F := by
        intro k hk
        rcases List.mem_append.mp hk with hk | hk
        · exact hCr k hk
        · simpa only [List.mem_singleton.mp hk] using hiF
      have htarget' : Prefix loc F B v z lam eta Q ((C++[i])++T) := by
        simpa only [List.append_assoc,List.singleton_append] using htarget
      have hvG' : Valid loc F B Q v z lam eta ((C++[i])++G) := by
        simpa only [List.append_assoc,List.singleton_append] using hvG
      obtain ⟨J,m,hm,hJ,hvJ,hwJ⟩ := ih (C++[i]) G hCi hGr hTr' htarget' hvG'
      have hUlen : U.length ≤ F.card := by
        have hh := regular_length hcur.1 (fun k hk => (List.mem_append.mp hk).elim (hCr k) (hUr k))
        simp only [List.length_append] at hh
        omega
      refine ⟨J,n+m,?_,hJ,?_,?_⟩
      · calc
          n+m ≤ (F.card+2)+T.length*(F.card+2) := Nat.add_le_add (by omega) hm
          _ = (i::T).length*(F.card+2) := by simp only [List.length_cons,Nat.add_mul,one_mul]; omega
      · simpa only [List.append_assoc,List.singleton_append] using hvJ
      · have hh := hw.trans (by simpa only [List.append_assoc,List.singleton_append] using hwJ)
        simpa only [List.append_assoc,List.singleton_append] using hh

theorem prune_suffix (loc : D → X) (F B Q : Finset X) (copy : X → X)
    (v z lam eta : ℝ) (hv : 0 < v) (hvsmall : v < 1/6) (hz : 0 < z)
    (hlam : 0 < lam) (hrow : ∀ k ∈ F, bidRow loc (1-3*v) z Q k ≤ lam)
    (C U : List X) (hCr : ∀ k ∈ C, k ∈ F) (hUr : ∀ k ∈ U, k ∈ F)
    (htarget : Valid loc F B Q v z lam eta C)
    (hcur : Valid loc F B Q v z lam eta (C++U)) :
    Walk loc F B Q copy v z lam eta U.length (C++U) C := by
  induction U with
  | nil =>
    simp only [List.append_nil,List.length_nil]
    exact Walk.nil (regular_good htarget hCr)
  | cons u U ih =>
    have ht : 0 ≤ 1-3*v := by linarith only [hvsmall]
    have hp : Prefix loc F B v z lam eta Q (C++U) :=
      hcur.1.sublist ((List.Sublist.cons u (List.Sublist.refl U)).append_left C)
    have hm : Maximal loc F (Q ∪ (C++U).toFinset) v z lam := by
      apply MaximalPrefixSelection.maximal_superset loc F (Q ∪ C.toFinset) _ v z lam lam
        hv hvsmall hz hlam
      · intro k hk
        exact (bidRow_antitone_open loc (1-3*v) z Q (Q ∪ C.toFinset) k ht
          Finset.subset_union_left).trans (hrow k hk)
      · exact htarget.2
      · exact le_rfl
      · simp only [List.toFinset_append]
        exact Finset.union_subset_union_right Finset.subset_union_left
    have hUr' : ∀ k ∈ U, k ∈ F := fun k hk => hUr k (List.mem_cons_of_mem u hk)
    have hw := ih hUr' ⟨hp,hm⟩
    have hgood : Good loc F B Q copy v z lam eta (C++u::U) := by
      apply regular_good hcur
      intro k hk
      exact (List.mem_append.mp hk).elim (hCr k) (hUr k)
    have hs := Step.remove (loc := loc) (F := F) (B := B) (Q := Q) (copy := copy)
      (v := v) (z := z) (lam := lam) C U [] u (hUr u (List.mem_cons_self ..))
      (Prefix.nil _) (by simp)
    simpa only [List.length_cons,List.append_nil] using Walk.cons hgood hs (by simpa using hw)

theorem regular_phase_path (loc : D → X) (F B Q : Finset X) (copy : X → X)
    (v z lam eta : ℝ) (hv : 0 < v) (hvsmall : v < 1/6) (hz : 0 < z)
    (hlam : 0 < lam) (heta : 0 ≤ eta) (hQ : Q ⊆ F ∪ B) (hdis : Disjoint F B)
    (hrow : ∀ k ∈ F, bidRow loc (1-3*v) z Q k ≤ lam)
    (hfresh : ∀ i ∈ F, copy i ∉ F ∪ B)
    (hco : ∀ i ∈ F, ∀ j, dist (loc j) i = dist (loc j) (copy i))
    (H J : List X) (hHr : ∀ k ∈ H, k ∈ F) (hJr : ∀ k ∈ J, k ∈ F)
    (hH : Valid loc F B Q v z lam eta H) (hJ : Valid loc F B Q v z lam eta J) :
    ∃ n : ℕ, n ≤ F.card*(F.card+3) ∧ Walk loc F B Q copy v z lam eta n J H := by
  obtain ⟨G,n,hn,hGr,hHG,hw⟩ := match_prefix loc F B Q copy v z lam eta hv hvsmall hz
    hlam heta hQ hdis hrow hfresh hco [] J H (by simp) hJr hHr (by simpa using hH.1)
      (by simpa using hJ)
  simp only [List.nil_append] at hHG hw
  have hw' := prune_suffix loc F B Q copy v z lam eta hv hvsmall hz hlam hrow H G hHr hGr hH hHG
  have hHlen := regular_length hH.1 hHr
  have hGlen : G.length ≤ F.card := by
    have hh := regular_length hHG.1 (fun k hk => (List.mem_append.mp hk).elim (hHr k) (hGr k))
    simp only [List.length_append] at hh
    omega
  refine ⟨n+G.length,?_,hw.trans hw'⟩
  calc
    n+G.length ≤ F.card*(F.card+2)+F.card :=
      Nat.add_le_add (hn.trans (Nat.mul_le_mul_right _ hHlen)) hGlen
    _ = F.card*(F.card+3) := by ring

end MetricKMedianRecovery.PhaseMergePath

end OAI
