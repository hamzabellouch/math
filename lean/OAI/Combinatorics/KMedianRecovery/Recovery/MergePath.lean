import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.Pool

namespace OAI

namespace MetricKMedianRecovery.RationalPhase
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion OrdinaryProducer

def completion {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v z lam : ℚ) (Q : Finset (Fin m)) : List (Fin m) :=
  (finish distance F v lam F.card ⟨Q,z,Vector.replicate d 0⟩).2.map Event.facility

lemma completion_spec {m d : ℕ} [PseudoMetricSpace (Fin m)]
    (loc : Fin d → Fin m) (distance : Fin m → Fin d → ℚ)
    (hd : ∀ f j,(distance f j:ℝ)=dist f (loc j))
    (F B Q : Finset (Fin m)) (v z lam : ℚ)
    (hv : (0:ℝ)<(v:ℝ)) (hv1 : (v:ℝ)<1/6) (hz : (0:ℝ)≤(z:ℝ)) (hQ : Q⊆F∪B) :
    Valid loc F B Q v z lam 0 (completion distance F v z lam Q) ∧
      (∀ i ∈ completion distance F v z lam Q, i ∈ F) ∧
      (completion distance F v z lam Q).length ≤ F.card := by
  let s : State m d := ⟨Q,z,Vector.replicate d 0⟩
  obtain ⟨hp,hr,ho⟩ := finish_prefix loc distance hd F B v lam hv hv1 F.card s hz hQ
  obtain ⟨_,hn,_,_,_,hz',hm⟩ := complete_spec loc distance hd F v lam hv hv1 s hz
  refine ⟨⟨hp,?_⟩,hr,?_⟩
  · have hphase : ((finish distance F v lam F.card s).1.phase:ℝ)=(z:ℝ) := congrArg Rat.cast hz'
    change ∀ i ∈ F, i ∉ Q ∪ (completion distance F v z lam Q).toFinset → _
    have ho' : (finish distance F v lam F.card s).1.opened =
        Q ∪ (completion distance F v z lam Q).toFinset := ho
    rw [←ho']
    simpa only [PhaseMaximal,State.real,hphase] using hm
  · simpa only [completion,List.length_map] using hn
end MetricKMedianRecovery.RationalPhase

namespace MetricKMedianRecovery.CanonicalMergePath
open PhaseSequence PhaseMergeSurgery PhaseMergePath
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

def CorrectCompletion (loc : D → X) (F : Finset X) (v z lam : ℝ)
    (complete : Finset X → List X) : Prop :=
  ∀ B Q, Q ⊆ F ∪ B → Valid loc F B Q v z lam 0 (complete Q) ∧
    (∀ i ∈ complete Q, i ∈ F)

lemma rational_correct {m d : ℕ} [PseudoMetricSpace (Fin m)]
    (loc : Fin d → Fin m) (distance : Fin m → Fin d → ℚ)
    (hd : ∀ f j,(distance f j:ℝ)=dist f (loc j)) (F : Finset (Fin m)) (v z lam : ℚ)
    (hv : (0:ℝ)<(v:ℝ)) (hv1 : (v:ℝ)<1/6) (hz : (0:ℝ)≤(z:ℝ)) :
    CorrectCompletion loc F v z lam (RationalPhase.completion distance F v z lam) := by
  intro B Q hQ
  have hh := RationalPhase.completion_spec loc distance hd F B Q v z lam hv hv1 hz hQ
  exact ⟨hh.1,hh.2.1⟩

lemma CorrectCompletion.retaining {loc : D → X} {F B Q : Finset X} {v z lam eta : ℝ}
    {complete : Finset X → List X} (hc : CorrectCompletion loc F v z lam complete)
    (heta : 0 ≤ eta) (hQ : Q ⊆ F ∪ B) (H : List X)
    (hH : Prefix loc F B v z lam eta Q H) (i f : X) (hiB : i ∉ B)
    (hf : f ∈ Q ∪ H.toFinset) (hco : ∀ j, dist (loc j) i = dist (loc j) f)
    (ht : 0 ≤ 1-3*v) (hlam : 0 < lam) :
    let G := complete (Q ∪ H.toFinset)
    (∀ k ∈ G, k ∈ F) ∧ i ∉ G ∧ Prefix loc F B v z lam 0 (Q ∪ H.toFinset) G ∧
      Valid loc F B Q v z lam eta (H++G) := by
  obtain ⟨⟨hG,hm⟩,hr⟩ := hc B (Q ∪ H.toFinset) (Finset.union_subset hQ hH.opened_subset)
  refine ⟨hr,exact_prefix_avoids_copy loc F B (Q ∪ H.toFinset) v z lam i f
    hiB hf hco ht hlam _ hG,hG,hH.append (prefix_exact_eta hG heta),?_⟩
  simpa only [List.toFinset_append,←Finset.union_assoc] using hm

inductive Path (loc : D → X) (F B Q : Finset X) (copy : X → X) (v z lam eta : ℝ) :
    List X → List (List X) → List X → Prop
  | nil {H} (h : Good loc F B Q copy v z lam eta H) : Path loc F B Q copy v z lam eta H [] H
  | cons {H G T J} (h : Good loc F B Q copy v z lam eta H)
      (e : Step loc F B Q copy v z lam H G)
      (t : Path loc F B Q copy v z lam eta G T J) :
      Path loc F B Q copy v z lam eta H (G::T) J

lemma Path.toWalk {loc : D → X} {F B Q : Finset X} {copy : X → X} {v z lam eta : ℝ}
    {H J : List X} {T : List (List X)} (h : Path loc F B Q copy v z lam eta H T J) :
    Walk loc F B Q copy v z lam eta T.length H J := by
  induction h with
  | nil h => exact .nil h
  | cons h e t ih => exact .cons h e ih

lemma Path.append {loc : D → X} {F B Q : Finset X} {copy : X → X} {v z lam eta : ℝ}
    {H J K : List X} {T U : List (List X)} (h : Path loc F B Q copy v z lam eta H T J)
    (h' : Path loc F B Q copy v z lam eta J U K) :
    Path loc F B Q copy v z lam eta H (T++U) K := by
  induction h with
  | nil => exact h'
  | cons h e t ih => exact .cons h e (ih h')

def deleteSuffix (complete : Finset X → List X) (Q : Finset X) (copy : X → X)
    (C : List X) (i : X) : List X → List X → List X × List (List X)
  | [],E => (E,[])
  | _u::U,E =>
    let A := complete (Q ∪ (C++U++copy i::E).toFinset)
    let r := deleteSuffix complete Q copy C i U (E++A)
    (r.1,(C++U++copy i::(E++A))::r.2)

omit [PseudoMetricSpace X] in
lemma deleteSuffix_length (complete : Finset X → List X) (Q : Finset X) (copy : X → X)
    (C : List X) (i : X) (U E : List X) :
    (deleteSuffix complete Q copy C i U E).2.length = U.length := by
  induction U generalizing E with
  | nil => rfl
  | cons u U ih => simp only [deleteSuffix,List.length_cons,ih]

theorem deleteSuffix_spec (loc : D → X) (F B Q : Finset X) (copy : X → X)
    (v z lam eta : ℝ) (complete : Finset X → List X)
    (hc : CorrectCompletion loc F v z lam complete) (heta : 0 ≤ eta) (hQ : Q ⊆ F ∪ B)
    (ht : 0 ≤ 1-3*v) (hlam : 0 < lam) (C U E : List X) (i : X)
    (hiF : i ∈ F) (hiB : i ∉ B) (hif : i ≠ copy i)
    (hco : ∀ j, dist (loc j) i = dist (loc j) (copy i))
    (hC : ∀ k ∈ C, k ∈ F) (hU : ∀ k ∈ U, k ∈ F) (hE : ∀ k ∈ E, k ∈ F)
    (hiE : i ∉ E)
    (hvalid : Valid loc F (insert (copy i) B) Q v z lam eta (C++U++copy i::E)) :
    let r := deleteSuffix complete Q copy C i U E
    (∀ k ∈ r.1, k ∈ F) ∧ i ∉ r.1 ∧
      Valid loc F (insert (copy i) B) Q v z lam eta (C++copy i::r.1) ∧
      Path loc F B Q copy v z lam eta (C++U++copy i::E) r.2 (C++copy i::r.1) := by
  induction U generalizing E with
  | nil =>
    have hv' : Valid loc F (insert (copy i) B) Q v z lam eta (C++copy i::E) := by
      simpa only [List.append_nil] using hvalid
    refine ⟨hE,hiE,hv',?_⟩
    simp only [deleteSuffix,List.append_nil]
    apply Path.nil
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
    let A := complete (Q ∪ (C++U++copy i::E).toFinset)
    obtain ⟨hAreg,hiA,hA,hvA⟩ := hc.retaining heta hQ' (C++U++copy i::E) hret i (copy i) hiB' hf hco ht hlam
    have hEA : ∀ k ∈ E++A, k ∈ F := by
      intro k hk
      exact (List.mem_append.mp hk).elim (hE k) (hAreg k)
    have hiEA : i ∉ E++A := by simpa only [List.mem_append,not_or] using ⟨hiE,hiA⟩
    have hvEA : Valid loc F (insert (copy i) B) Q v z lam eta (C++U++copy i::(E++A)) := by
      simpa only [A,List.append_assoc,List.cons_append] using hvA
    obtain ⟨hG,hiG,hvG,hw⟩ := ih (E++A) hUr hEA hiEA hvEA
    refine ⟨hG,hiG,hvG,?_⟩
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
      (by simpa only [A,List.append_assoc] using prefix_free_mono hA (insert_subset_pool hiF)) hAreg
    apply Path.cons hg
    · simpa only [A,List.append_assoc,List.cons_append] using hs
    · exact hw

lemma Path.last_good {loc : D → X} {F B Q : Finset X} {copy : X → X} {v z lam eta : ℝ}
    {H J : List X} {T : List (List X)} (h : Path loc F B Q copy v z lam eta H T J) :
    Good loc F B Q copy v z lam eta J := h.toWalk.last_good

def advancePrefix (complete : Finset X → List X) (Q : Finset X) (copy : X → X)
    (C U : List X) (i : X) : List X × List (List X) :=
  let r := deleteSuffix complete Q copy C i U []
  (r.1,(C++U++[copy i])::(r.2++[C++i::r.1]))

omit [PseudoMetricSpace X] in
lemma advancePrefix_length (complete : Finset X → List X) (Q : Finset X) (copy : X → X)
    (C U : List X) (i : X) :
    (advancePrefix complete Q copy C U i).2.length=U.length+2 := by
  simp only [advancePrefix,List.length_cons,List.length_append,List.length_nil,
    deleteSuffix_length]

 theorem advancePrefix_spec (loc : D → X) (F B Q : Finset X) (copy : X → X)
    (v z lam eta : ℝ) (complete : Finset X → List X)
    (hc : CorrectCompletion loc F v z lam complete)
    (hv : 0 < v) (hvsmall : v < 1/6) (hz : 0 < z)
    (hlam : 0 < lam) (heta : 0 ≤ eta) (hQ : Q ⊆ F ∪ B)
    (hrow : ∀ k ∈ F, bidRow loc (1-3*v) z Q k ≤ lam)
    (C U : List X) (i : X) (hiF : i ∈ F) (hiB : i ∉ B)
    (hfresh : copy i ∉ F ∪ B) (hco : ∀ j, dist (loc j) i = dist (loc j) (copy i))
    (hC : Prefix loc F B v z lam eta Q C)
    (hi : Entry loc F B (Q ∪ C.toFinset) v z lam eta i)
    (hCr : ∀ k ∈ C, k ∈ F) (hUr : ∀ k ∈ U, k ∈ F)
    (hcur : Valid loc F B Q v z lam eta (C++U)) :
    let r := advancePrefix complete Q copy C U i
    (∀ k ∈ r.1, k ∈ F) ∧ Valid loc F B Q v z lam eta (C++i::r.1) ∧
      Path loc F B Q copy v z lam eta (C++U) r.2 (C++i::r.1) := by
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
  let r := deleteSuffix complete Q copy C i U []
  obtain ⟨hGr,hiG,hvalid,hw⟩ := deleteSuffix_spec loc F B Q copy v z lam eta complete hc
    heta hQ ht hlam C U [] i hiF hiB hir hco hCr hUr (by simp) (by simp) happ
  have hfC : copy i ∉ Q ∪ C.toFinset := by
    intro hm
    apply hf
    rcases Finset.mem_union.mp hm with hm | hm
    · exact Finset.mem_union_left _ hm
    · exact Finset.mem_union_right _ (by simpa only [List.toFinset_append] using Finset.mem_union_left U.toFinset hm)
  have hvG := regularize loc F B Q v z lam eta C r.1 i (copy i) hiF hfF hfC hiG hco hC hi hvalid
  have hCG : ∀ k ∈ C++i::r.1, k ∈ F := by
    intro k hk
    rcases List.mem_append.mp hk with hk | hk
    · exact hCr k hk
    · rcases List.mem_cons.mp hk with rfl | hk
      · exact hiF
      · exact hGr k hk
  have hi' : i ∉ Q ∪ (C++r.1).toFinset := by
    simp only [List.toFinset_append,Finset.mem_union,not_or,List.mem_toFinset]
    exact ⟨fun h => hi.1 (Finset.mem_union_left _ h),
      fun h => hi.1 (Finset.mem_union_right _ (List.mem_toFinset.mpr h)),hiG⟩
  have hs := Step.replace (loc := loc) (B := B) (copy := copy) (v := v) (z := z)
    (lam := lam) C r.1 i hiF hi'
  have hw' := hw.append (Path.cons hw.last_good hs (Path.nil (regular_good hvG hCG)))
  have hw'' := Path.cons (regular_good hcur hr) (Step.add _ i hiF) hw'
  exact ⟨hGr,hvG,hw''⟩

def matchPrefix (complete : Finset X → List X) (Q : Finset X) (copy : X → X)
    : List X → List X → List X → List X × List (List X)
  | _C,U,[] => (U,[])
  | C,U,i::T =>
    let a := advancePrefix complete Q copy C U i
    let b := matchPrefix complete Q copy (C++[i]) a.1 T
    (b.1,a.2++b.2)

 theorem matchPrefix_spec (loc : D → X) (F B Q : Finset X) (copy : X → X)
    (v z lam eta : ℝ) (complete : Finset X → List X)
    (hc : CorrectCompletion loc F v z lam complete)
    (hv : 0 < v) (hvsmall : v < 1/6) (hz : 0 < z)
    (hlam : 0 < lam) (heta : 0 ≤ eta) (hQ : Q ⊆ F ∪ B) (hdis : Disjoint F B)
    (hrow : ∀ k ∈ F, bidRow loc (1-3*v) z Q k ≤ lam)
    (hfresh : ∀ i ∈ F, copy i ∉ F ∪ B)
    (hco : ∀ i ∈ F, ∀ j, dist (loc j) i = dist (loc j) (copy i))
    (C U T : List X) (hCr : ∀ k ∈ C, k ∈ F) (hUr : ∀ k ∈ U, k ∈ F)
    (hTr : ∀ k ∈ T, k ∈ F)
    (htarget : Prefix loc F B v z lam eta Q (C++T))
    (hcur : Valid loc F B Q v z lam eta (C++U)) :
    let r := matchPrefix complete Q copy C U T
    r.2.length ≤ T.length*(F.card+2) ∧ (∀ k ∈ r.1, k ∈ F) ∧
      Valid loc F B Q v z lam eta (C++T++r.1) ∧
      Path loc F B Q copy v z lam eta (C++U) r.2 (C++T++r.1) := by
  induction T generalizing C U with
  | nil =>
    refine ⟨by simp [matchPrefix],hUr,?_,?_⟩
    · simpa only [matchPrefix,List.append_nil] using hcur
    · simp only [matchPrefix,List.append_nil]
      apply Path.nil
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
      let a := advancePrefix complete Q copy C U i
      obtain ⟨hGr,hvG,hw⟩ := advancePrefix_spec loc F B Q copy v z lam eta complete hc
        hv hvsmall hz hlam heta hQ hrow C U i hiF hiB (hfresh i hiF) (hco i hiF)
        hC hi hCr hUr hcur
      have hCi : ∀ k ∈ C++[i], k ∈ F := by
        intro k hk
        rcases List.mem_append.mp hk with hk | hk
        · exact hCr k hk
        · simpa only [List.mem_singleton.mp hk] using hiF
      have htarget' : Prefix loc F B v z lam eta Q ((C++[i])++T) := by
        simpa only [List.append_assoc,List.singleton_append] using htarget
      obtain ⟨hm,hJ,hvJ,hwJ⟩ := ih (C++[i]) a.1 hCi hGr hTr' htarget'
        (by simpa only [a,List.append_assoc,List.singleton_append] using hvG)
      have hUlen : U.length ≤ F.card := by
        have hh := regular_length hcur.1 (fun k hk => (List.mem_append.mp hk).elim (hCr k) (hUr k))
        simp only [List.length_append] at hh
        omega
      refine ⟨?_,hJ,?_,?_⟩
      · change (a.2 ++ (matchPrefix complete Q copy (C++[i]) a.1 T).2).length ≤ _
        rw [List.length_append]
        have ha : a.2.length = U.length+2 := advancePrefix_length ..
        rw [ha,List.length_cons,Nat.add_mul,one_mul]
        omega
      · simpa only [matchPrefix,List.append_assoc,List.singleton_append] using hvJ
      · have hh := hw.append (by simpa only [a,List.append_assoc,List.singleton_append] using hwJ)
        simpa only [matchPrefix,List.append_assoc,List.singleton_append] using hh

def pruneSuffix (C : List X) : List X → List (List X)
  | [] => []
  | _::U => (C++U)::pruneSuffix C U

omit [PseudoMetricSpace X] [DecidableEq X] in
lemma pruneSuffix_length (C U : List X) : (pruneSuffix C U).length=U.length := by
  induction U with
  | nil => rfl
  | cons u U ih => simp only [pruneSuffix,List.length_cons,ih]

 theorem pruneSuffix_spec (loc : D → X) (F B Q : Finset X) (copy : X → X)
    (v z lam eta : ℝ) (hv : 0 < v) (hvsmall : v < 1/6) (hz : 0 < z)
    (hlam : 0 < lam) (hrow : ∀ k ∈ F, bidRow loc (1-3*v) z Q k ≤ lam)
    (C U : List X) (hCr : ∀ k ∈ C, k ∈ F) (hUr : ∀ k ∈ U, k ∈ F)
    (htarget : Valid loc F B Q v z lam eta C)
    (hcur : Valid loc F B Q v z lam eta (C++U)) :
    Path loc F B Q copy v z lam eta (C++U) (pruneSuffix C U) C := by
  induction U with
  | nil =>
    simp only [List.append_nil,pruneSuffix]
    exact Path.nil (regular_good htarget hCr)
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
    simpa only [pruneSuffix,List.append_nil] using Path.cons hgood hs (by simpa only [List.append_nil] using hw)

def regularPath (complete : Finset X → List X) (Q : Finset X) (copy : X → X)
    (H J : List X) : List (List X) :=
  let r := matchPrefix complete Q copy [] J H
  r.2 ++ pruneSuffix H r.1

 theorem regularPath_spec (loc : D → X) (F B Q : Finset X) (copy : X → X)
    (v z lam eta : ℝ) (complete : Finset X → List X)
    (hc : CorrectCompletion loc F v z lam complete)
    (hv : 0 < v) (hvsmall : v < 1/6) (hz : 0 < z)
    (hlam : 0 < lam) (heta : 0 ≤ eta) (hQ : Q ⊆ F ∪ B) (hdis : Disjoint F B)
    (hrow : ∀ k ∈ F, bidRow loc (1-3*v) z Q k ≤ lam)
    (hfresh : ∀ i ∈ F, copy i ∉ F ∪ B)
    (hco : ∀ i ∈ F, ∀ j, dist (loc j) i = dist (loc j) (copy i))
    (H J : List X) (hHr : ∀ k ∈ H, k ∈ F) (hJr : ∀ k ∈ J, k ∈ F)
    (hH : Valid loc F B Q v z lam eta H) (hJ : Valid loc F B Q v z lam eta J) :
    let T := regularPath complete Q copy H J
    T.length ≤ F.card*(F.card+3) ∧ Path loc F B Q copy v z lam eta J T H := by
  let r := matchPrefix complete Q copy [] J H
  obtain ⟨hn,hGr,hHG,hw⟩ := matchPrefix_spec loc F B Q copy v z lam eta complete hc
    hv hvsmall hz hlam heta hQ hdis hrow hfresh hco [] J H (by simp) hJr hHr
      (by simpa only [List.nil_append] using hH.1) (by simpa only [List.nil_append] using hJ)
  simp only [List.nil_append] at hHG hw
  have hw' := pruneSuffix_spec loc F B Q copy v z lam eta hv hvsmall hz hlam hrow H r.1 hHr hGr hH hHG
  have hHlen := regular_length hH.1 hHr
  have hGlen : r.1.length ≤ F.card := by
    change (matchPrefix complete Q copy [] J H).1.length ≤ F.card
    have hh := regular_length hHG.1 (fun k hk => (List.mem_append.mp hk).elim (hHr k) (hGr k))
    simp only [List.length_append] at hh
    omega
  refine ⟨?_,hw.append hw'⟩
  change (r.2++pruneSuffix H r.1).length ≤ _
  rw [List.length_append,pruneSuffix_length]
  calc
    r.2.length+r.1.length ≤ F.card*(F.card+2)+F.card :=
      Nat.add_le_add (hn.trans (Nat.mul_le_mul_right _ hHlen)) hGlen
    _ = F.card*(F.card+3) := by ring

end MetricKMedianRecovery.CanonicalMergePath

end OAI
