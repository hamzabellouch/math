import Mathlib

namespace OAI

namespace MatchingFPRAS.Transport

variable {V L : Type*}

abbrev ColoredEdge (V L : Type*) := {e : Sym2 V × L // ¬ e.1.IsDiag}

namespace ColoredEdge

variable (e : ColoredEdge V L)

def Incident (v : V) : Prop := v ∈ e.val.1

def color : L := e.val.2

lemma exists_incident : ∃ v, e.Incident v := by
  change ∃ v, v ∈ e.val.1
  exact Sym2.inductionOn e.val.1 fun a b => ⟨a, by simp⟩

end ColoredEdge

def Allowed (bags : V → Finset L) (e : ColoredEdge V L) : Prop :=
  ∀ v, e.Incident v → e.color ∈ bags v

abbrev BagEdge (bags : V → Finset L) := {e : ColoredEdge V L // Allowed bags e}

namespace BagEdge

variable {bags : V → Finset L}

def Incident (e : BagEdge bags) (v : V) : Prop := e.val.Incident v

lemma exists_incident (e : BagEdge bags) : ∃ v, e.Incident v := e.val.exists_incident

end BagEdge

variable {E : Type*} [DecidableEq V] [DecidableEq E] (inc : E → V → Prop)

def MatchingOn (M : Finset E) (U : Finset V) : Prop :=
  (∀ e ∈ M, ∀ v, inc e v → v ∈ U) ∧
  (∀ v ∈ U, ∃! e, e ∈ M ∧ inc e v)

namespace MatchingOn

variable {inc} {M P Q : Finset E} {U W : Finset V}

omit [DecidableEq V] [DecidableEq E] in
lemma unique (hM : MatchingOn inc M U) {v : V} (hv : v ∈ U)
    {e f : E} (he : e ∈ M) (hev : inc e v) (hf : f ∈ M) (hfv : inc f v) : e = f := by
  obtain ⟨g, _, hg⟩ := hM.2 v hv
  exact (hg e ⟨he, hev⟩).trans (hg f ⟨hf, hfv⟩).symm

omit [DecidableEq V] [DecidableEq E] in
lemma edge_mem_of_incident (hM : MatchingOn inc M U) (hP : MatchingOn inc P W)
    (hsub : P ⊆ M) {e : E} (he : e ∈ M) {v : V} (hv : v ∈ W) (hev : inc e v) : e ∈ P := by
  obtain ⟨f, ⟨hf, hfv⟩, _⟩ := hP.2 v hv
  have eq : e = f := hM.unique (hM.1 e he v hev) he hev (hsub hf) hfv
  exact eq ▸ hf

omit [DecidableEq V] [DecidableEq E] in
lemma disjoint_edges (hM : MatchingOn inc M U) (hP : MatchingOn inc P W)
    (hinc : ∀ e, ∃ v, inc e v) (hdis : Disjoint U W) : Disjoint M P := by
  apply Finset.disjoint_left.mpr
  intro e he hf
  obtain ⟨v, hv⟩ := hinc e
  exact Finset.disjoint_left.mp hdis (hM.1 e he v hv) (hP.1 e hf v hv)

lemma union (hM : MatchingOn inc M U) (hP : MatchingOn inc P W)
    (hdis : Disjoint U W) : MatchingOn inc (M ∪ P) (U ∪ W) := by
  refine ⟨?_, ?_⟩
  · intro e he v hev
    rcases Finset.mem_union.mp he with he | he
    · exact Finset.mem_union_left _ (hM.1 e he v hev)
    · exact Finset.mem_union_right _ (hP.1 e he v hev)
  · intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · obtain ⟨e, ⟨he, hev⟩, hu⟩ := hM.2 v hv
      refine ⟨e, ⟨Finset.mem_union_left _ he, hev⟩, ?_⟩
      intro f hf
      rcases Finset.mem_union.mp hf.1 with hfM | hfP
      · exact hu f ⟨hfM, hf.2⟩
      · exact False.elim (Finset.disjoint_left.mp hdis hv (hP.1 f hfP v hf.2))
    · obtain ⟨e, ⟨he, hev⟩, hu⟩ := hP.2 v hv
      refine ⟨e, ⟨Finset.mem_union_right _ he, hev⟩, ?_⟩
      intro f hf
      rcases Finset.mem_union.mp hf.1 with hfM | hfP
      · exact False.elim (Finset.disjoint_left.mp hdis (hM.1 f hfM v hf.2) hv)
      · exact hu f ⟨hfP, hf.2⟩

lemma sdiff (hM : MatchingOn inc M U) (hP : MatchingOn inc P W) (hsub : P ⊆ M) :
    MatchingOn inc (M \ P) (U \ W) := by
  refine ⟨?_, ?_⟩
  · intro e he v hev
    obtain ⟨heM, heP⟩ := Finset.mem_sdiff.mp he
    refine Finset.mem_sdiff.mpr ⟨hM.1 e heM v hev, ?_⟩
    intro hv
    exact heP (hM.edge_mem_of_incident hP hsub heM hv hev)
  · intro v hv
    obtain ⟨hvU, hvW⟩ := Finset.mem_sdiff.mp hv
    obtain ⟨e, ⟨he, hev⟩, hu⟩ := hM.2 v hvU
    have heP : e ∉ P := fun hp => hvW (hP.1 e hp v hev)
    refine ⟨e, ⟨Finset.mem_sdiff.mpr ⟨he, heP⟩, hev⟩, ?_⟩
    intro f hf
    exact hu f ⟨(Finset.mem_sdiff.mp hf.1).1, hf.2⟩

lemma replace (hM : MatchingOn inc M U) (hP : MatchingOn inc P W)
    (hQ : MatchingOn inc Q W) (hsub : P ⊆ M) (hWU : W ⊆ U) :
    MatchingOn inc ((M \ P) ∪ Q) U := by
  have h := (hM.sdiff hP hsub).union hQ Finset.sdiff_disjoint
  simpa only [Finset.sdiff_union_of_subset hWU] using h

lemma context_disjoint (hM : MatchingOn inc M U) (hP : MatchingOn inc P W)
    (hQ : MatchingOn inc Q W) (hsub : P ⊆ M)
    (hinc : ∀ e, ∃ v, inc e v) : Disjoint (M \ P) Q :=
  (hM.sdiff hP hsub).disjoint_edges hQ hinc Finset.sdiff_disjoint

lemma replace_context (hM : MatchingOn inc M U) (hP : MatchingOn inc P W)
    (hQ : MatchingOn inc Q W) (hsub : P ⊆ M)
    (hinc : ∀ e, ∃ v, inc e v) : ((M \ P) ∪ Q) \ Q = M \ P := by
  have hd := hM.context_disjoint hP hQ hsub hinc
  ext e
  simp only [Finset.mem_sdiff, Finset.mem_union]
  constructor
  · rintro ⟨h | h, hn⟩
    · exact h
    · exact (hn h).elim
  · intro h
    exact ⟨Or.inl h, fun he => Finset.disjoint_left.mp hd (Finset.mem_sdiff.mpr h) he⟩

end MatchingOn

lemma union_val_add {F G : Finset E} (h : Disjoint F G) :
    (F ∪ G).val = F.val + G.val := by
  rw [← Finset.disjUnion_eq_union F G h, Finset.disjUnion_val]

lemma sdiff_val_add {F G : Finset E} (h : G ⊆ F) :
    (F \ G).val + G.val = F.val := by
  rw [← union_val_add Finset.sdiff_disjoint, Finset.sdiff_union_of_subset h]

lemma pattern_interchange {M N P Q : Finset E} {U W : Finset V}
    (hM : MatchingOn inc M U) (hN : MatchingOn inc N U)
    (hP : MatchingOn inc P W) (hQ : MatchingOn inc Q W)
    (hPM : P ⊆ M) (hQN : Q ⊆ N) (hWU : W ⊆ U)
    (hinc : ∀ e, ∃ v, inc e v) :
    MatchingOn inc ((M \ P) ∪ Q) U ∧
    MatchingOn inc ((N \ Q) ∪ P) U ∧
    ((M \ P) ∪ Q).val + ((N \ Q) ∪ P).val = M.val + N.val := by
  refine ⟨hM.replace hP hQ hPM hWU, hN.replace hQ hP hQN hWU, ?_⟩
  rw [union_val_add (hM.context_disjoint hP hQ hPM hinc),
    union_val_add (hN.context_disjoint hQ hP hQN hinc)]
  calc
    _ = ((M \ P).val + P.val) + ((N \ Q).val + Q.val) := by ac_rfl
    _ = _ := by rw [sdiff_val_add hPM, sdiff_val_add hQN]

lemma pattern_interchange_weight {R : Type*} [CommMonoid R] (w : E → R)
    {M N P Q : Finset E} {U W : Finset V}
    (hM : MatchingOn inc M U) (hN : MatchingOn inc N U)
    (hP : MatchingOn inc P W) (hQ : MatchingOn inc Q W)
    (hPM : P ⊆ M) (hQN : Q ⊆ N) (hinc : ∀ e, ∃ v, inc e v) :
    (∏ e ∈ (M \ P) ∪ Q, w e) * (∏ e ∈ (N \ Q) ∪ P, w e) =
      (∏ e ∈ M, w e) * (∏ e ∈ N, w e) := by
  rw [Finset.prod_union (hM.context_disjoint hP hQ hPM hinc),
    Finset.prod_union (hN.context_disjoint hQ hP hQN hinc)]
  calc
    _ = ((∏ e ∈ M \ P, w e) * ∏ e ∈ P, w e) *
        ((∏ e ∈ N \ Q, w e) * ∏ e ∈ Q, w e) := by ac_rfl
    _ = _ := by rw [Finset.prod_sdiff hPM, Finset.prod_sdiff hQN]

lemma pattern_interchange_inverse {M P Q : Finset E} {U W : Finset V}
    (hM : MatchingOn inc M U) (hP : MatchingOn inc P W) (hQ : MatchingOn inc Q W)
    (hPM : P ⊆ M) (hinc : ∀ e, ∃ v, inc e v) :
    ((((M \ P) ∪ Q) \ Q) ∪ P) = M := by
  rw [hM.replace_context hP hQ hPM hinc, Finset.sdiff_union_of_subset hPM]

def pathPattern (edges : ℕ → E) (lo hi : ℕ) : Finset E :=
  ((Finset.Ico lo hi).filter (fun i => i % 2 = lo % 2)).image edges

lemma pathPattern_matching (vertices : ℕ → V) (edges : ℕ → E) (lo hi : ℕ)
    (hlohi : lo < hi) (hodd : (hi - lo) % 2 = 1)
    (hinj : Set.InjOn vertices (Set.Icc lo hi))
    (hedges : ∀ i, lo ≤ i → i < hi →
      ∀ v, inc (edges i) v ↔ v = vertices i ∨ v = vertices (i + 1)) :
    MatchingOn inc (pathPattern edges lo hi) ((Finset.Icc lo hi).image vertices) := by
  classical
  refine ⟨?_, ?_⟩
  · intro e he v hv
    obtain ⟨i, hi', rfl⟩ := Finset.mem_image.mp he
    obtain ⟨hirange, hiParity⟩ := Finset.mem_filter.mp hi'
    obtain ⟨hil, hih⟩ := Finset.mem_Ico.mp hirange
    rcases (hedges i hil hih v).mp hv with rfl | rfl
    · exact Finset.mem_image.mpr ⟨i, Finset.mem_Icc.mpr ⟨hil, by omega⟩, rfl⟩
    · exact Finset.mem_image.mpr ⟨i + 1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, rfl⟩
  · intro v hv
    obtain ⟨k, hkrange, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨hkl, hkh⟩ := Finset.mem_Icc.mp hkrange
    have hex : ∃ i, lo ≤ i ∧ i < hi ∧ i % 2 = lo % 2 ∧ (k = i ∨ k = i + 1) := by
      by_cases hk : k % 2 = lo % 2
      · exact ⟨k, hkl, by omega, hk, Or.inl rfl⟩
      · exact ⟨k - 1, by omega, by omega, by omega, Or.inr (by omega)⟩
    obtain ⟨i, hil, hih, hip, hki⟩ := hex
    have hem : edges i ∈ pathPattern edges lo hi :=
      Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hil, hih⟩, hip⟩, rfl⟩
    have hev : inc (edges i) (vertices k) := by
      apply (hedges i hil hih _).mpr
      exact hki.imp (congrArg vertices) (congrArg vertices)
    refine ⟨edges i, ⟨hem, hev⟩, ?_⟩
    intro f hf
    obtain ⟨j, hj', rfl⟩ := Finset.mem_image.mp hf.1
    obtain ⟨hjrange, hjp⟩ := Finset.mem_filter.mp hj'
    obtain ⟨hjl, hjh⟩ := Finset.mem_Ico.mp hjrange
    have hkj : k = j ∨ k = j + 1 := by
      rcases (hedges j hjl hjh _).mp hf.2 with h | h
      · exact Or.inl (hinj ⟨hkl, hkh⟩ ⟨hjl, by omega⟩ h)
      · exact Or.inr (hinj ⟨hkl, hkh⟩ ⟨by omega, by omega⟩ h)
    have hji : j = i := by omega
    exact congrArg edges hji

omit [DecidableEq E] in
lemma singleton_matching (e : E) (a b : V)
    (he : ∀ v, inc e v ↔ v = a ∨ v = b) : MatchingOn inc {e} {a, b} := by
  classical
  refine ⟨?_, ?_⟩
  · intro f hf v hv
    have hf' : f = e := Finset.mem_singleton.mp hf
    subst f
    simpa only [Finset.mem_insert, Finset.mem_singleton] using (he v).mp hv
  · intro v hv
    refine ⟨e, ⟨Finset.mem_singleton_self _, ?_⟩, ?_⟩
    · apply (he v).mpr
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hv
    · intro f hf
      exact Finset.mem_singleton.mp hf.1

omit [DecidableEq V] [DecidableEq E] in
lemma empty_matching : MatchingOn inc ∅ ∅ := by simp [MatchingOn]

lemma closedPattern_matching (vertices : ℕ → V) (edges : ℕ → E) (lo hi : ℕ)
    (hlong : lo + 3 ≤ hi) (hodd : (hi - lo) % 2 = 1)
    (hinj : Set.InjOn vertices (Set.Icc lo hi))
    (hedges : ∀ i, lo ≤ i → i < hi →
      ∀ v, inc (edges i) v ↔ v = vertices i ∨ v = vertices (i + 1))
    (chord : E) (hchord : ∀ v, inc chord v ↔ v = vertices lo ∨ v = vertices hi) :
    MatchingOn inc (pathPattern edges (lo + 1) (hi - 1) ∪ {chord})
      ((Finset.Icc lo hi).image vertices) := by
  have hT : MatchingOn inc (pathPattern edges (lo + 1) (hi - 1))
      ((Finset.Icc (lo + 1) (hi - 1)).image vertices) := by
    apply pathPattern_matching inc vertices edges (lo + 1) (hi - 1)
    · omega
    · omega
    · intro i hi' j hj' heq
      simp only [Set.mem_Icc] at hi' hj'
      exact hinj ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ heq
    · intro i hi' hi'' v
      exact hedges i (by omega) (by omega) v
  have hc := singleton_matching inc chord (vertices lo) (vertices hi) hchord
  have hd : Disjoint ((Finset.Icc (lo + 1) (hi - 1)).image vertices)
      {vertices lo, vertices hi} := by
    apply Finset.disjoint_left.mpr
    intro v hv hw
    obtain ⟨i, hi', rfl⟩ := Finset.mem_image.mp hv
    have hir := Finset.mem_Icc.mp hi'
    rcases Finset.mem_insert.mp hw with h | h
    · have heq := hinj ⟨by omega, by omega⟩ ⟨le_rfl, by omega⟩ h
      omega
    · have heq := hinj ⟨by omega, by omega⟩ ⟨by omega, le_rfl⟩
        (Finset.mem_singleton.mp h)
      omega
  have hs : ((Finset.Icc (lo + 1) (hi - 1)).image vertices) ∪
      {vertices lo, vertices hi} = (Finset.Icc lo hi).image vertices := by
    ext v
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_Icc,
      Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (⟨i, hi', rfl⟩ | h | h)
      · exact ⟨i, ⟨by omega, by omega⟩, rfl⟩
      · exact ⟨lo, ⟨le_rfl, by omega⟩, h.symm⟩
      · exact ⟨hi, ⟨by omega, le_rfl⟩, h.symm⟩
    · rintro ⟨i, hi', rfl⟩
      by_cases hl : i = lo
      · exact Or.inr (Or.inl (congrArg vertices hl))
      by_cases hh : i = hi
      · exact Or.inr (Or.inr (congrArg vertices hh))
      exact Or.inl ⟨i, ⟨by omega, by omega⟩, rfl⟩
  simpa only [hs] using hT.union hc hd

lemma pathPattern_boundary (edges : ℕ → E) (lo hi : ℕ)
    (hlong : lo + 3 ≤ hi) (hodd : (hi - lo) % 2 = 1) :
    pathPattern edges lo hi = pathPattern edges (lo + 2) (hi - 2) ∪
      {edges lo, edges (hi - 1)} := by
  have hidx : (Finset.Ico lo hi).filter (fun i => i % 2 = lo % 2) =
      ((Finset.Ico (lo + 2) (hi - 2)).filter (fun i => i % 2 = (lo + 2) % 2)) ∪
        {lo, hi - 1} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_union,
      Finset.mem_insert, Finset.mem_singleton]
    omega
  unfold pathPattern
  rw [hidx, Finset.image_union]
  simp only [Finset.image_insert, Finset.image_singleton]

lemma repairedThrough_matching (vertices : ℕ → V) (edges : ℕ → E) (lo hi : ℕ)
    (hlong : lo + 3 ≤ hi) (hodd : (hi - lo) % 2 = 1)
    (hinj : Set.InjOn vertices (Set.Icc lo hi))
    (hedges : ∀ i, lo ≤ i → i < hi →
      ∀ v, inc (edges i) v ↔ v = vertices i ∨ v = vertices (i + 1))
    (repair : E)
    (hrepair : ∀ v, inc repair v ↔ v = vertices (lo + 1) ∨ v = vertices (hi - 1)) :
    MatchingOn inc (pathPattern edges (lo + 2) (hi - 2) ∪ {repair})
      ((Finset.Icc (lo + 1) (hi - 1)).image vertices) := by
  have hT : MatchingOn inc (pathPattern edges (lo + 2) (hi - 2))
      ((Finset.Icc (lo + 2) (hi - 2)).image vertices) := by
    by_cases h : lo + 2 < hi - 2
    · apply pathPattern_matching inc vertices edges (lo + 2) (hi - 2) h
      · omega
      · intro i hi' j hj' heq
        simp only [Set.mem_Icc] at hi' hj'
        exact hinj ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ heq
      · intro i hi' hi'' v
        exact hedges i (by omega) (by omega) v
    · have hl : hi - 2 < lo + 2 := by omega
      have he : Finset.Ico (lo + 2) (hi - 2) = ∅ := Finset.Ico_eq_empty_of_le (by omega)
      have he' : Finset.Icc (lo + 2) (hi - 2) = ∅ := Finset.Icc_eq_empty_of_lt hl
      simpa [pathPattern, he, he'] using (empty_matching (V := V) (E := E) inc)
  have hc := singleton_matching inc repair (vertices (lo + 1)) (vertices (hi - 1)) hrepair
  have hd : Disjoint ((Finset.Icc (lo + 2) (hi - 2)).image vertices)
      {vertices (lo + 1), vertices (hi - 1)} := by
    apply Finset.disjoint_left.mpr
    intro v hv hw
    obtain ⟨i, hi', rfl⟩ := Finset.mem_image.mp hv
    have hir := Finset.mem_Icc.mp hi'
    rcases Finset.mem_insert.mp hw with h | h
    · have heq := hinj ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ h
      omega
    · have heq := hinj ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
        (Finset.mem_singleton.mp h)
      omega
  have hs : ((Finset.Icc (lo + 2) (hi - 2)).image vertices) ∪
      {vertices (lo + 1), vertices (hi - 1)} =
      (Finset.Icc (lo + 1) (hi - 1)).image vertices := by
    ext v
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_Icc,
      Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (⟨i, hi', rfl⟩ | h | h)
      · exact ⟨i, ⟨by omega, by omega⟩, rfl⟩
      · exact ⟨lo + 1, ⟨le_rfl, by omega⟩, h.symm⟩
      · exact ⟨hi - 1, ⟨by omega, le_rfl⟩, h.symm⟩
    · rintro ⟨i, hi', rfl⟩
      by_cases hl : i = lo + 1
      · exact Or.inr (Or.inl (congrArg vertices hl))
      by_cases hh : i = hi - 1
      · exact Or.inr (Or.inr (congrArg vertices hh))
      exact Or.inl ⟨i, ⟨by omega, by omega⟩, rfl⟩
  simpa only [hs] using hT.union hc hd

def overlayLineGraph (S : Finset E) : SimpleGraph E where
  Adj e f := e ≠ f ∧ e ∈ S ∧ f ∈ S ∧ ∃ v, inc e v ∧ inc f v
  symm := ⟨by
    intro e f h
    rcases h with ⟨h, he, hf, v, hev, hfv⟩
    exact ⟨h.symm, hf, he, v, hfv, hev⟩⟩
  loopless := ⟨by intro e h; exact h.1 rfl⟩

lemma union_eq_of_multiset_union_eq {M N A B : Finset E}
    (h : M.val + N.val = A.val + B.val) : M ∪ N = A ∪ B := by
  ext e
  have he := congrArg (fun s : Multiset E => e ∈ s) h
  simpa only [Multiset.mem_add, Finset.mem_val, Finset.mem_union] using (iff_of_eq he)

omit [DecidableEq V] in
lemma layer_agreement_adj {M N A B : Finset E} {U : Finset V}
    (hM : MatchingOn inc M U) (hN : MatchingOn inc N U)
    (hA : MatchingOn inc A U) (hB : MatchingOn inc B U)
    (hu : M ∪ N = A ∪ B) {e f : E}
    (hadj : (overlayLineGraph inc (M ∪ N)).Adj e f)
    (he : e ∈ M ↔ e ∈ A) : f ∈ M ↔ f ∈ A := by
  obtain ⟨hne, heu, hfu, v, hev, hfv⟩ := hadj
  by_cases heM : e ∈ M
  · have heA := he.mp heM
    have hfM : f ∉ M := fun hf =>
      hne (hM.unique (hM.1 e heM v hev) heM hev hf hfv)
    have hfA : f ∉ A := fun hf =>
      hne (hA.unique (hA.1 e heA v hev) heA hev hf hfv)
    exact iff_of_false hfM hfA
  · have heA : e ∉ A := fun h => heM (he.mpr h)
    have heN : e ∈ N := (Finset.mem_union.mp heu).resolve_left heM
    have heB : e ∈ B := (Finset.mem_union.mp (hu ▸ heu)).resolve_left heA
    have hfN : f ∉ N := fun hf =>
      hne (hN.unique (hN.1 e heN v hev) heN hev hf hfv)
    have hfB : f ∉ B := fun hf =>
      hne (hB.unique (hB.1 e heB v hev) heB hev hf hfv)
    exact iff_of_true ((Finset.mem_union.mp hfu).resolve_right hfN)
      ((Finset.mem_union.mp (hu ▸ hfu)).resolve_right hfB)

omit [DecidableEq V] in
lemma layer_agreement_reachable {M N A B : Finset E} {U : Finset V}
    (hM : MatchingOn inc M U) (hN : MatchingOn inc N U)
    (hA : MatchingOn inc A U) (hB : MatchingOn inc B U)
    (hu : M ∪ N = A ∪ B) {e f : E}
    (hr : (overlayLineGraph inc (M ∪ N)).Reachable e f)
    (he : e ∈ M ↔ e ∈ A) : f ∈ M ↔ f ∈ A := by
  have hrel := (SimpleGraph.reachable_iff_reflTransGen _ _).mp hr
  clear hr
  induction hrel with
  | refl => exact he
  | tail hpath hadj ih => exact layer_agreement_adj inc hM hN hA hB hu hadj ih

omit [DecidableEq V] in
lemma pair_reconstruction {M N A B : Finset E} {U : Finset V}
    (hM : MatchingOn inc M U) (hN : MatchingOn inc N U)
    (hA : MatchingOn inc A U) (hB : MatchingOn inc B U)
    (hu : M.val + N.val = A.val + B.val) (anchor : E)
    (hbit : anchor ∈ M ↔ anchor ∈ A)
    (hout : ∀ e ∈ M ∪ N, ¬ (overlayLineGraph inc (M ∪ N)).Reachable anchor e →
      (e ∈ M ↔ e ∈ A)) : M = A ∧ N = B := by
  have hset := union_eq_of_multiset_union_eq hu
  have hMA : M = A := by
    ext e
    by_cases hr : (overlayLineGraph inc (M ∪ N)).Reachable anchor e
    · exact layer_agreement_reachable inc hM hN hA hB hset hr hbit
    · by_cases he : e ∈ M ∪ N
      · exact hout e he hr
      · have heM : e ∉ M := fun hm => he (Finset.mem_union_left _ hm)
        have heA : e ∉ A := fun ha => he (hset.symm ▸ Finset.mem_union_left B ha)
        exact iff_of_false heM heA
  refine ⟨hMA, Finset.val_injective ?_⟩
  rw [hMA] at hu
  exact add_left_cancel hu

omit [DecidableEq E] in
lemma multiset_product_comparison (w : E → ℝ) (hw : ∀ e, 0 < w e)
    (A : ℝ) (hA : 0 ≤ A) (drop add : Multiset E) (hcard : drop.card = add.card)
    (hcompare : ∀ e ∈ drop, ∀ f ∈ add, w e ≤ A * w f) :
    (drop.map w).prod ≤ A ^ drop.card * (add.map w).prod := by
  induction drop using Multiset.induction_on generalizing add with
  | empty =>
      have ha : add = 0 := Multiset.card_eq_zero.mp (by simpa using hcard.symm)
      subst add
      simp
  | @cons e drop ih =>
      obtain ⟨f, hf⟩ := Multiset.card_pos_iff_exists_mem.mp
        (show 0 < add.card by simp only [Multiset.card_cons] at hcard; omega)
      obtain ⟨add', rfl⟩ := Multiset.exists_cons_of_mem hf
      have hcard' : drop.card = add'.card := by simpa using hcard
      have hi := ih add' hcard' (fun a ha b hb =>
        hcompare a (Multiset.mem_cons_of_mem ha) b (Multiset.mem_cons_of_mem hb))
      have he := hcompare e (Multiset.mem_cons_self _ _) f (Multiset.mem_cons_self _ _)
      have hp : 0 ≤ (drop.map w).prod := le_of_lt <| Multiset.prod_pos (by
        intro z hz
        obtain ⟨a, _, rfl⟩ := Multiset.mem_map.mp hz
        exact hw a)
      have hb : 0 ≤ A * w f := mul_nonneg hA (le_of_lt (hw f))
      simpa only [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, pow_succ,
        mul_assoc, mul_left_comm, mul_comm] using mul_le_mul he hi hp hb

omit [DecidableEq E] in
lemma four_edge_weight_bound (w : E → ℝ) (hw : ∀ e, 0 < w e)
    (A : ℝ) (hA : 1 ≤ A) (input output drop add : Multiset E)
    (hcons : input + add = output + drop)
    (hcard : drop.card = add.card) (hfour : drop.card ≤ 4)
    (hcompare : ∀ e ∈ drop, ∀ f ∈ add, w e ≤ A * w f) :
    (input.map w).prod ≤ A ^ 4 * (output.map w).prod := by
  have hnonneg : 0 ≤ A := by linarith
  have hc := multiset_product_comparison w hw A hnonneg drop add hcard hcompare
  have ha : 0 < (add.map w).prod := Multiset.prod_pos (by
    intro z hz
    obtain ⟨e, _, rfl⟩ := Multiset.mem_map.mp hz
    exact hw e)
  have ho : 0 ≤ (output.map w).prod := le_of_lt <| Multiset.prod_pos (by
    intro z hz
    obtain ⟨e, _, rfl⟩ := Multiset.mem_map.mp hz
    exact hw e)
  have hweight := congrArg (fun s : Multiset E => (s.map w).prod) hcons
  simp only [Multiset.map_add, Multiset.prod_add] at hweight
  have hpow : A ^ drop.card ≤ A ^ 4 := pow_le_pow_right₀ hA hfour
  have hc' : (drop.map w).prod ≤ A ^ 4 * (add.map w).prod :=
    hc.trans (mul_le_mul_of_nonneg_right hpow (le_of_lt ha))
  apply (mul_le_mul_iff_left₀ ha).mp
  calc
    _ = (output.map w).prod * (drop.map w).prod := hweight
    _ ≤ (output.map w).prod * (A ^ 4 * (add.map w).prod) :=
      mul_le_mul_of_nonneg_left hc' ho
    _ = _ := by ring

structure OddPath where
  length : ℕ
  positive : 0 < length
  odd : length % 2 = 1
  vertex : ℕ → V
  edge : ℕ → E
  simple : Set.InjOn vertex (Set.Icc 0 length)
  incidence : ∀ i, i < length → ∀ v,
    inc (edge i) v ↔ v = vertex i ∨ v = vertex (i + 1)

end MatchingFPRAS.Transport

end OAI
