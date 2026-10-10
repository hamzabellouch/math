import OAI.Computability.LoopMatching.ChoiceCounts

namespace OAI

/-! Polynomial-time approximation of weighted matchings with singleton loops. -/

noncomputable section
open scoped BigOperators
namespace LoopMatching

def SupportedMatching (G : Input) (j : ℕ) :=
  {N : (BinaryMatching.completeGraph (expand G j).n).Matching //
    ∀ e ∈ N.val, e.val.1.val < G.n}

def oldVertex (G : Input) (j : ℕ) (v : Fin G.n) : Fin (expand G j).n :=
  ⟨v.val, by have := v.isLt; simp only [expand_n]; omega⟩

def dummyVertex (G : Input) (j : ℕ) (d : Fin j) : Fin (expand G j).n :=
  ⟨G.n + d.val, by have := d.isLt; simp only [expand_n]; omega⟩

@[simp] lemma incident_oldPair (G : Input) (j : ℕ) (v : Fin G.n)
    (e : BinaryMatching.Pair G.n) :
    (BinaryMatching.completeGraph (expand G j).n).Incident
      (oldVertex G j v) (oldPair G j e) ↔
    (BinaryMatching.completeGraph G.n).Incident v e := by
  simp [MatchingEntropy.LooplessGraph.Incident, BinaryMatching.completeGraph,
    oldVertex, oldPair, Fin.ext_iff]

lemma oldPair_injective (G : Input) (j : ℕ) : Function.Injective (oldPair G j) := by
  intro e f h
  apply Subtype.ext
  apply Prod.ext <;> apply Fin.ext
  · exact congrArg (fun p => p.val.1.val) h
  · exact congrArg (fun p => p.val.2.val) h

lemma crossPair_injective (G : Input) (j : ℕ) {v w : Fin G.n} {d c : Fin j}
    (h : crossPair G j v d = crossPair G j w c) : v = w ∧ d = c := by
  constructor
  · apply Fin.ext
    exact congrArg (fun p => p.val.1.val) h
  · apply Fin.ext
    have hh := congrArg (fun p => p.val.2.val) h
    dsimp [crossPair] at hh
    omega

lemma oldPair_ne_crossPair (G : Input) (j : ℕ) (e : BinaryMatching.Pair G.n)
    (v : Fin G.n) (d : Fin j) : oldPair G j e ≠ crossPair G j v d := by
  intro h
  have hh := congrArg (fun p => p.val.2.val) h
  have he := e.val.2.isLt
  dsimp [oldPair, crossPair] at hh
  omega

lemma matching_edge_unique (G : Input) (j : ℕ)
    (N : (BinaryMatching.completeGraph (expand G j).n).Matching)
    (v : Fin (expand G j).n) (e f : BinaryMatching.Pair (expand G j).n)
    (he : e ∈ N.val) (hf : f ∈ N.val)
    (hve : (BinaryMatching.completeGraph (expand G j).n).Incident v e)
    (hvf : (BinaryMatching.completeGraph (expand G j).n).Incident v f) : e = f := by
  obtain ⟨a, ha, hu⟩ := N.property v
  exact (hu e ⟨he,hve⟩).trans (hu f ⟨hf,hvf⟩).symm

def restrictMatching (G : Input) (j : ℕ) (N : SupportedMatching G j) :
    PartialMatching G.n := by
  classical
  refine ⟨Finset.univ.filter (fun e => oldPair G j e ∈ N.val.val), ?_⟩
  intro v e he f hf hve hvf
  apply oldPair_injective G j
  exact matching_edge_unique G j N.val (oldVertex G j v) _ _
    (Finset.mem_filter.mp he).2 (Finset.mem_filter.mp hf).2
    ((incident_oldPair G j v e).mpr hve) ((incident_oldPair G j v f).mpr hvf)

@[simp] lemma mem_restrictMatching (G : Input) (j : ℕ) (N : SupportedMatching G j)
    (e : BinaryMatching.Pair G.n) :
    e ∈ (restrictMatching G j N).val ↔ oldPair G j e ∈ N.val.val := by
  simp [restrictMatching]

lemma exists_crossPartner (G : Input) (j : ℕ) (N : SupportedMatching G j)
    (d : Fin j) : ∃ v : Fin G.n, crossPair G j v d ∈ N.val.val := by
  obtain ⟨e,⟨he,hi⟩,hu⟩ := N.val.property (dummyVertex G j d)
  have hl := N.property e he
  have hr : e.val.2.val = G.n + d.val := by
    rcases hi with hi | hi
    · have hh := congrArg Fin.val hi
      dsimp [BinaryMatching.completeGraph, dummyVertex] at hh
      omega
    · exact congrArg Fin.val hi
  let v : Fin G.n := ⟨e.val.1.val,hl⟩
  refine ⟨v, ?_⟩
  have hh : crossPair G j v d = e := by
    apply Subtype.ext
    apply Prod.ext <;> apply Fin.ext
    · rfl
    · exact hr.symm
  simpa only [hh] using he

def crossPartner (G : Input) (j : ℕ) (N : SupportedMatching G j) (d : Fin j) : Fin G.n :=
  Classical.choose (exists_crossPartner G j N d)

lemma crossPartner_mem (G : Input) (j : ℕ) (N : SupportedMatching G j) (d : Fin j) :
    crossPair G j (crossPartner G j N d) d ∈ N.val.val :=
  Classical.choose_spec (exists_crossPartner G j N d)

lemma crossPartner_eq (G : Input) (j : ℕ) (N : SupportedMatching G j)
    (v : Fin G.n) (d : Fin j) (hv : crossPair G j v d ∈ N.val.val) :
    crossPartner G j N d = v := by
  have he := matching_edge_unique G j N.val (dummyVertex G j d) _ _
    (crossPartner_mem G j N d) hv (Or.inr rfl) (Or.inr rfl)
  exact (crossPair_injective G j he).1

lemma crossPartner_uncovered (G : Input) (j : ℕ) (N : SupportedMatching G j) (d : Fin j) :
    crossPartner G j N d ∈ loopVertices (restrictMatching G j N) := by
  classical
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  intro e he hi
  apply oldPair_ne_crossPair G j e (crossPartner G j N d) d
  exact matching_edge_unique G j N.val (oldVertex G j (crossPartner G j N d)) _ _
    ((mem_restrictMatching G j N e).mp he) (crossPartner_mem G j N d)
    ((incident_oldPair G j _ e).mpr hi) (Or.inl rfl)

lemma crossPartner_injective (G : Input) (j : ℕ) (N : SupportedMatching G j) :
    Function.Injective (crossPartner G j N) := by
  intro d c h
  have he := matching_edge_unique G j N.val (oldVertex G j (crossPartner G j N d))
    _ _ (crossPartner_mem G j N d) (crossPartner_mem G j N c)
    (Or.inl rfl) (Or.inl (congrArg (oldVertex G j) h.symm))
  exact (crossPair_injective G j he).2

lemma crossPartner_surjective (G : Input) (j : ℕ) (N : SupportedMatching G j)
    (v : loopVertices (restrictMatching G j N)) :
    ∃ d : Fin j, crossPartner G j N d = v.val := by
  classical
  obtain ⟨e,⟨he,hi⟩,hu⟩ := N.val.property (oldVertex G j v.val)
  have hl := N.property e he
  have hr : G.n ≤ e.val.2.val := by
    by_contra hh
    have hright : e.val.2.val < G.n := by omega
    let f : BinaryMatching.Pair G.n :=
      ⟨(⟨e.val.1.val,hl⟩,⟨e.val.2.val,hright⟩), e.property⟩
    have hef : oldPair G j f = e := by
      apply Subtype.ext
      apply Prod.ext <;> apply Fin.ext <;> rfl
    have hf : f ∈ (restrictMatching G j N).val := by
      rw [mem_restrictMatching, hef]
      exact he
    have huv := (Finset.mem_filter.mp v.property).2
    apply huv f hf
    apply (incident_oldPair G j v.val f).mp
    simpa only [hef] using hi
  have hleft : e.val.1.val = v.val.val := by
    rcases hi with hi | hi
    · exact congrArg Fin.val hi
    · have hh := congrArg Fin.val hi
      have hv := v.val.isLt
      dsimp [BinaryMatching.completeGraph,oldVertex] at hh
      omega
  let d : Fin j := ⟨e.val.2.val-G.n, by
    have he2 := e.val.2.isLt
    simp only [expand_n] at he2
    omega⟩
  have hed : crossPair G j v.val d = e := by
    apply Subtype.ext
    apply Prod.ext <;> apply Fin.ext
    · exact hleft.symm
    · dsimp [crossPair,d]
      omega
  exact ⟨d,crossPartner_eq G j N v.val d (by simpa only [hed] using he)⟩

def dummyEquiv (G : Input) (j : ℕ) (N : SupportedMatching G j) :
    Fin j ≃ ↥(loopVertices (restrictMatching G j N)) :=
  Equiv.ofBijective (fun d => ⟨crossPartner G j N d,crossPartner_uncovered G j N d⟩)
    ⟨fun d c h => crossPartner_injective G j N (congrArg Subtype.val h), by
      intro v
      obtain ⟨d,hd⟩ := crossPartner_surjective G j N v
      exact ⟨d,Subtype.ext hd⟩⟩

@[simp] lemma incident_cross_old (G : Input) (j : ℕ) (v w : Fin G.n) (d : Fin j) :
    (BinaryMatching.completeGraph (expand G j).n).Incident
      (oldVertex G j v) (crossPair G j w d) ↔ w = v := by
  have hv := v.isLt
  simp only [MatchingEntropy.LooplessGraph.Incident, BinaryMatching.completeGraph,
    crossPair, oldVertex, Fin.ext_iff]
  omega

@[simp] lemma incident_cross_dummy (G : Input) (j : ℕ) (v : Fin G.n) (d c : Fin j) :
    (BinaryMatching.completeGraph (expand G j).n).Incident
      (dummyVertex G j d) (crossPair G j v c) ↔ c = d := by
  have hv := v.isLt
  simp only [MatchingEntropy.LooplessGraph.Incident, BinaryMatching.completeGraph,
    crossPair, dummyVertex, Fin.ext_iff]
  omega

@[simp] lemma not_incident_old_dummy (G : Input) (j : ℕ)
    (e : BinaryMatching.Pair G.n) (d : Fin j) :
    ¬ (BinaryMatching.completeGraph (expand G j).n).Incident
      (dummyVertex G j d) (oldPair G j e) := by
  have h1 := e.val.1.isLt
  have h2 := e.val.2.isLt
  simp only [MatchingEntropy.LooplessGraph.Incident, BinaryMatching.completeGraph,
    oldPair, dummyVertex, Fin.ext_iff]
  omega

def assembledEdges (G : Input) (j : ℕ) (M : PartialMatching G.n)
    (b : Fin j ≃ ↥(loopVertices M)) : Finset (BinaryMatching.Pair (expand G j).n) := by
  classical
  exact M.val.image (oldPair G j) ∪ Finset.univ.image (fun d => crossPair G j (b d).val d)

lemma mem_assembledEdges (G : Input) (j : ℕ) (M : PartialMatching G.n)
    (b : Fin j ≃ ↥(loopVertices M)) (e : BinaryMatching.Pair (expand G j).n) :
    e ∈ assembledEdges G j M b ↔
      (∃ f ∈ M.val, oldPair G j f = e) ∨ (∃ d, crossPair G j (b d).val d = e) := by
  classical
  simp only [assembledEdges, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]

lemma assembledEdges_perfect (G : Input) (j : ℕ) (M : PartialMatching G.n)
    (b : Fin j ≃ ↥(loopVertices M)) :
    (BinaryMatching.completeGraph (expand G j).n).IsPerfectMatching
      (assembledEdges G j M b) := by
  classical
  intro x
  by_cases hx : x.val < G.n
  · let v : Fin G.n := ⟨x.val,hx⟩
    have hxv : x = oldVertex G j v := by apply Fin.ext; rfl
    rw [hxv]
    by_cases hv : ∃ e ∈ M.val, (BinaryMatching.completeGraph G.n).Incident v e
    · obtain ⟨e,he,hi⟩ := hv
      refine ⟨oldPair G j e, ⟨?_,(incident_oldPair G j v e).mpr hi⟩, ?_⟩
      · exact (mem_assembledEdges G j M b _).mpr (Or.inl ⟨e,he,rfl⟩)
      · intro f hf
        rcases (mem_assembledEdges G j M b f).mp hf.1 with ⟨a,ha,rfl⟩ | ⟨d,rfl⟩
        · exact congrArg (oldPair G j)
            (M.property v a ha e he ((incident_oldPair G j v a).mp hf.2) hi)
        · have hbv := (incident_cross_old G j v (b d).val d).mp hf.2
          have hloop := (Finset.mem_filter.mp (b d).property).2
          exact False.elim (hloop e he (by simpa only [hbv] using hi))
    · have hvloop : v ∈ loopVertices M := by
        simp only [loopVertices,Finset.mem_filter,Finset.mem_univ,true_and]
        simpa only [not_exists,not_and] using hv
      let d := b.symm ⟨v,hvloop⟩
      have hbd : (b d).val = v := congrArg Subtype.val (b.apply_symm_apply _)
      refine ⟨crossPair G j (b d).val d, ⟨?_, ?_⟩, ?_⟩
      · exact (mem_assembledEdges G j M b _).mpr (Or.inr ⟨d,rfl⟩)
      · exact (incident_cross_old G j v (b d).val d).mpr hbd
      · intro f hf
        rcases (mem_assembledEdges G j M b f).mp hf.1 with ⟨a,ha,rfl⟩ | ⟨c,rfl⟩
        · exact False.elim (hv ⟨a,ha,(incident_oldPair G j v a).mp hf.2⟩)
        · have hbc := (incident_cross_old G j v (b c).val c).mp hf.2
          have hcd : c = d := b.injective (Subtype.ext (hbc.trans hbd.symm))
          subst c
          rfl
  · let d : Fin j := ⟨x.val-G.n,by have := x.isLt; simp only [expand_n] at this; omega⟩
    have hxd : x = dummyVertex G j d := by apply Fin.ext; dsimp [dummyVertex,d]; omega
    rw [hxd]
    refine ⟨crossPair G j (b d).val d, ⟨?_,Or.inr rfl⟩, ?_⟩
    · exact (mem_assembledEdges G j M b _).mpr (Or.inr ⟨d,rfl⟩)
    · intro f hf
      rcases (mem_assembledEdges G j M b f).mp hf.1 with ⟨a,ha,rfl⟩ | ⟨c,rfl⟩
      · exact False.elim (not_incident_old_dummy G j a d hf.2)
      · have hcd := (incident_cross_dummy G j (b c).val d c).mp hf.2
        subst c
        rfl

def assembleMatching (G : Input) (j : ℕ) (M : PartialMatching G.n)
    (b : Fin j ≃ ↥(loopVertices M)) : SupportedMatching G j := by
  refine ⟨⟨assembledEdges G j M b,assembledEdges_perfect G j M b⟩,?_⟩
  intro e he
  rcases (mem_assembledEdges G j M b e).mp he with ⟨a,ha,rfl⟩ | ⟨d,rfl⟩
  · exact a.val.1.isLt
  · exact (b d).val.isLt

lemma restrict_assemble (G : Input) (j : ℕ) (M : PartialMatching G.n)
    (b : Fin j ≃ ↥(loopVertices M)) :
    restrictMatching G j (assembleMatching G j M b) = M := by
  classical
  apply Subtype.ext
  ext e
  rw [mem_restrictMatching]
  change oldPair G j e ∈ assembledEdges G j M b ↔ e ∈ M.val
  rw [mem_assembledEdges]
  constructor
  · rintro (⟨a,ha,hea⟩ | ⟨d,hd⟩)
    · exact (oldPair_injective G j hea) ▸ ha
    · exact False.elim (oldPair_ne_crossPair G j e (b d).val d hd.symm)
  · intro he
    exact Or.inl ⟨e,he,rfl⟩

lemma crossPartner_assemble (G : Input) (j : ℕ) (M : PartialMatching G.n)
    (b : Fin j ≃ ↥(loopVertices M)) (d : Fin j) :
    crossPartner G j (assembleMatching G j M b) d = (b d).val := by
  apply crossPartner_eq
  exact (mem_assembledEdges G j M b _).mpr (Or.inr ⟨d,rfl⟩)

lemma supported_edge_cases (G : Input) (j : ℕ) (N : SupportedMatching G j)
    (e : BinaryMatching.Pair (expand G j).n) (he : e ∈ N.val.val) :
    (∃ f ∈ (restrictMatching G j N).val, oldPair G j f = e) ∨
      (∃ d, crossPair G j (crossPartner G j N d) d = e) := by
  have hl := N.property e he
  by_cases hr : e.val.2.val < G.n
  · let f : BinaryMatching.Pair G.n :=
      ⟨(⟨e.val.1.val,hl⟩,⟨e.val.2.val,hr⟩),e.property⟩
    have hf : oldPair G j f = e := by
      apply Subtype.ext; apply Prod.ext <;> apply Fin.ext <;> rfl
    exact Or.inl ⟨f,(mem_restrictMatching G j N f).mpr (by simpa only [hf] using he),hf⟩
  · let d : Fin j := ⟨e.val.2.val-G.n,by
      have := e.val.2.isLt; simp only [expand_n] at this; omega⟩
    let v : Fin G.n := ⟨e.val.1.val,hl⟩
    have hf : crossPair G j v d = e := by
      apply Subtype.ext; apply Prod.ext <;> apply Fin.ext
      · rfl
      · dsimp [crossPair,d]; omega
    have hv := crossPartner_eq G j N v d (by simpa only [hf] using he)
    exact Or.inr ⟨d,by simpa only [hv] using hf⟩

lemma assemble_restrict (G : Input) (j : ℕ) (N : SupportedMatching G j) :
    assembleMatching G j (restrictMatching G j N) (dummyEquiv G j N) = N := by
  classical
  apply Subtype.ext
  apply Subtype.ext
  ext e
  change e ∈ assembledEdges G j (restrictMatching G j N) (dummyEquiv G j N) ↔ e ∈ N.val.val
  rw [mem_assembledEdges]
  constructor
  · rintro (⟨f,hf,rfl⟩ | ⟨d,rfl⟩)
    · exact (mem_restrictMatching G j N f).mp hf
    · exact crossPartner_mem G j N d
  · exact supported_edge_cases G j N e

instance supportedMatchingFintype (G : Input) (j : ℕ) : Fintype (SupportedMatching G j) := by
  classical
  unfold SupportedMatching
  exact Fintype.ofFinite _

def assembleMatchingEquiv (G : Input) (j : ℕ) :
    ((M : PartialMatching G.n) × (Fin j ≃ ↥(loopVertices M))) ≃ SupportedMatching G j :=
  Equiv.ofBijective (fun z => assembleMatching G j z.1 z.2) ⟨by
    rintro ⟨M,b⟩ ⟨M',b'⟩ h
    have hm : M = M' := by
      have hh := congrArg (restrictMatching G j) h
      simpa only [restrict_assemble] using hh
    cases hm
    change assembleMatching G j M b = assembleMatching G j M b' at h
    have hb : b = b' := by
      apply Equiv.ext
      intro d
      apply Subtype.ext
      rw [← crossPartner_assemble G j M b d, h, crossPartner_assemble]
    cases hb
    rfl,
    fun N => ⟨⟨restrictMatching G j N,dummyEquiv G j N⟩,assemble_restrict G j N⟩⟩

def supportedMatchingEquiv (G : Input) (j : ℕ) :
    SupportedMatching G j ≃ ((M : PartialMatching G.n) × (Fin j ≃ ↥(loopVertices M))) :=
  (assembleMatchingEquiv G j).symm

lemma supportedMatchingEquiv_fst (G : Input) (j : ℕ) (N : SupportedMatching G j) :
    (supportedMatchingEquiv G j N).1 = restrictMatching G j N := by
  have hh := congrArg (restrictMatching G j) ((assembleMatchingEquiv G j).apply_symm_apply N)
  change restrictMatching G j (assembleMatching G j
    (supportedMatchingEquiv G j N).1 (supportedMatchingEquiv G j N).2) = _ at hh
  simpa only [restrict_assemble] using hh

def supportedEdgeEquiv (G : Input) (j : ℕ) (N : SupportedMatching G j) :
    (↥(restrictMatching G j N).val ⊕ Fin j) ≃ ↥N.val.val :=
  Equiv.ofBijective (fun x => match x with
    | Sum.inl e => ⟨oldPair G j e.val,(mem_restrictMatching G j N e.val).mp e.property⟩
    | Sum.inr d => ⟨crossPair G j (crossPartner G j N d) d,crossPartner_mem G j N d⟩)
    ⟨by
      intro x y h
      have hh := congrArg Subtype.val h
      cases x with
      | inl e =>
        cases y with
        | inl f => exact congrArg Sum.inl (Subtype.ext (oldPair_injective G j hh))
        | inr d => exact False.elim (oldPair_ne_crossPair G j e.val _ d hh)
      | inr d =>
        cases y with
        | inl e => exact False.elim (oldPair_ne_crossPair G j e.val _ d hh.symm)
        | inr c => exact congrArg Sum.inr (crossPair_injective G j hh).2,
      by
        intro e
        rcases supported_edge_cases G j N e.val e.property with ⟨f,hf,he⟩ | ⟨d,he⟩
        · exact ⟨Sum.inl ⟨f,hf⟩,Subtype.ext he⟩
        · exact ⟨Sum.inr d,Subtype.ext he⟩⟩

lemma supported_matching_weight (G : Input) (j : ℕ) (N : SupportedMatching G j) :
    (∏ e ∈ N.val.val, BinaryMatching.multiplicity (expand G j) e) =
      weight G (restrictMatching G j N) := by
  classical
  rw [← Finset.prod_coe_sort]
  have hprod := Fintype.prod_equiv (supportedEdgeEquiv G j N)
    (fun x => match x with
      | Sum.inl e => BinaryMatching.multiplicity G.ordinary e.val
      | Sum.inr d => loopMultiplicity G (crossPartner G j N d))
    (fun e : N.val.val => BinaryMatching.multiplicity (expand G j) e.val)
    (by
      intro x
      cases x with
      | inl e =>
        change BinaryMatching.multiplicity G.ordinary e.val =
          BinaryMatching.multiplicity (expand G j) (oldPair G j e.val)
        exact (multiplicity_expand_old G j e.val).symm
      | inr d =>
        change loopMultiplicity G (crossPartner G j N d) =
          BinaryMatching.multiplicity (expand G j) (crossPair G j (crossPartner G j N d) d)
        exact (multiplicity_expand_cross G j (crossPartner G j N d) d).symm)
  rw [← hprod,Fintype.prod_sum_type]
  have hloop := Fintype.prod_equiv (dummyEquiv G j N)
    (fun d => loopMultiplicity G (crossPartner G j N d))
    (fun v => loopMultiplicity G v.val) (fun _ => rfl)
  rw [hloop]
  simp only [Finset.prod_coe_sort,weight]

lemma unsupported_matching_weight_zero (G : Input) (j : ℕ)
    (N : (BinaryMatching.completeGraph (expand G j).n).Matching)
    (h : ¬ ∀ e ∈ N.val, e.val.1.val < G.n) :
    (∏ e ∈ N.val, BinaryMatching.multiplicity (expand G j) e) = 0 := by
  classical
  push Not at h
  obtain ⟨e,he,hl⟩ := h
  have hright := e.val.2.isLt
  have hleft := e.val.1.isLt
  have hlt := e.property
  simp only [expand_n] at hright hleft
  let f : BinaryMatching.Pair j :=
    ⟨(⟨e.val.1.val-G.n,by omega⟩,⟨e.val.2.val-G.n,by omega⟩),by
      change e.val.1.val-G.n < e.val.2.val-G.n
      change e.val.1.val < e.val.2.val at hlt
      omega⟩
  have hf : dummyPair G j f = e := by
    apply Subtype.ext
    apply Prod.ext <;> apply Fin.ext <;> dsimp [dummyPair,f] <;> omega
  apply Finset.prod_eq_zero he
  rw [← hf,multiplicity_expand_dummy]

end LoopMatching

end

end OAI
