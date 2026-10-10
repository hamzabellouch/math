import OAI.Computability.WitnessedChoice.TreeCorrection

namespace OAI


namespace WitnessedSeparation.Grid

noncomputable section

open Classical WitnessedChoice WitnessedChoice.BGS Hereditary RelationPools

variable {n : ℕ} {b : Vertex n → Scalar}

namespace QuotedGrid

open QuotedTerm QuotedFormula SourceSyntax SourceProgram

attribute [local irreducible] QuotedTerm.nextEdges QuotedTerm.tree SourceSyntax.cycleRelations

lemma fundamentalPool_in_cycleSet (p : Polynomial ℝ) (hp : GridResources p b)
    (α : Fin 4 → Vertex n) (hα : AnchoredTree.Resolving (boxGraph n) α)
    (x : Finset (Σ e : Edge n, LocalGroup e)) (hn : 1 ≤ n) :
    (anchoredParents α).fundamentalPool (leastEdges α (remainingEdges (anchoredParents α).treeEdges x)) ⊆
      SourceProgram.program.body.cycleSet (atomInput b) p
        (tupleCode (List.ofFn (vertexCode b ∘ α))) (edgeState x) := by
  let R := distancesCode b (boxGraph n)
  let T := ofFinset ((anchoredParents α).treeEdges.image (edgeCode b))
  let H := connTableCode b (anchoredParents α).treeEdges
  let env₀ : Fin 3 → HF (Atom b) := Fin.cons R
    (Fin.cons (stateCode (edgeState x)) (Fin.cons (tupleCode (List.ofFn (vertexCode b ∘ α))) Fin.elim0))
  let env₁ : Fin 4 → HF (Atom b) := Fin.cons T env₀
  let env : Fin 5 → HF (Atom b) := Fin.cons H env₁
  have ht : (tree (var 2) QuotedTerm.vertexBlocks QuotedTerm.edgeBlocks (var 0)).meaning
      (atomInput b) env₀ = T :=
    meaning_tree env₀ (var 2) _ _ (var 0) α hα rfl
      (quoted_vertexBlocks hn env₀) (quoted_edgeBlocks env₀) rfl hn
  have hh : (SourceProgram.connTable QuotedTerm.vertexBlocks (var 0)).value
      (atomInput b) p env₁ = H :=
    value_connTable env₁ _ _ (anchoredParents α).treeEdges p hp
      (quoted_vertexBlocks hn env₁) rfl hn
  have hv : SourceProgram.cycles.value (atomInput b) p
      (Fin.cons (stateCode (edgeState x)) (Fin.cons (tupleCode (List.ofFn (vertexCode b ∘ α))) Fin.elim0)) =
      (cycleRelations QuotedTerm.vertexBlocks QuotedTerm.edgeBlocks
        (faces QuotedTerm.vertexBlocks QuotedTerm.edgeBlocks) (var 2) (var 1) (var 0)
        (nextEdges (var 4) QuotedTerm.vertexBlocks QuotedTerm.edgeBlocks (var 2) (var 1) (var 3))).meaning
        (atomInput b) env := by
    rw [SourceProgram.cycles,CPTTerm.value_letIn,value_distances _ p hp hn,
      CPTTerm.value_letIn,CPTTerm.value_quoted]
    change ((SourceProgram.connTable QuotedTerm.vertexBlocks (var 0)).letIn _).value (atomInput b) p
      (Fin.cons ((tree (var 2) QuotedTerm.vertexBlocks QuotedTerm.edgeBlocks (var 0)).meaning (atomInput b) env₀) env₀) = _
    rw [ht,CPTTerm.value_letIn]
    change (CPTTerm.quoted _).value (atomInput b) p
      (Fin.cons ((SourceProgram.connTable QuotedTerm.vertexBlocks (var 0)).value (atomInput b) p env₁) env₁) = _
    rw [hh,CPTTerm.value_quoted]
  have hV := quoted_vertexBlocks (b := b) hn env
  have hE := quoted_edgeBlocks (b := b) env
  have hN := meaning_nextEdges env (var 4) QuotedTerm.vertexBlocks QuotedTerm.edgeBlocks (var 2)
    (var 1) (var 3) α (anchoredParents α).treeEdges x hα rfl hV hE rfl rfl rfl hn
  intro r hr
  change r ∈ (elements (SourceProgram.cycles.value (atomInput b) p _)).image decodeRelation
  rw [hv]
  refine Finset.mem_image.mpr ⟨relationCode r,?_,decodeRelation_code r⟩
  apply fundamentalPool_in_cycles env QuotedTerm.vertexBlocks QuotedTerm.edgeBlocks
    (faces QuotedTerm.vertexBlocks QuotedTerm.edgeBlocks) (var 2) (var 1) (var 0) _
    (anchoredParents α) _ hV hE (mem_faces env _ _ hV hE hn) rfl rfl rfl hN _ hn r hr
  intro e he
  exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp (Finset.mem_filter.mp he).1).1).2

end QuotedGrid

end

end WitnessedSeparation.Grid


section

namespace WitnessedChoice.RelationPools

noncomputable section

open Classical WitnessedSeparation

variable {A : Type} [Fintype A]

lemma witnessPool_mono (B : ℕ) (S : Input A) (valid : Prop)
    (C D : Finset A → Finset (Relation A)) (x : Finset A) (hCD : C x ⊆ D x) :
    witnessPool B S valid C x ⊆ witnessPool B S valid D x := by
  unfold witnessPool
  split_ifs
  · intro g hg
    rcases Finset.mem_insert.mp hg with hg | hg
    · exact Finset.mem_insert.mpr (Or.inl hg)
    · apply Finset.mem_insert_of_mem
      simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hg ⊢
      obtain ⟨hf,l,hl,c,hc,he⟩ := hg
      exact ⟨hf,l,hl,c,hCD hc,he⟩
  · exact Finset.Subset.refl _

end

end WitnessedChoice.RelationPools

namespace WitnessedSeparation.Grid

noncomputable section

open Classical WitnessedChoice WitnessedChoice.BGS Hereditary RelationPools

variable {n : ℕ} {b : Vertex n → Scalar}

namespace QuotedGrid

open SourceProgram

lemma selection_transitive (p : Polynomial ℝ) (hp : GridResources p b)
    (α : Fin 4 → Vertex n) (hα : AnchoredTree.Resolving (boxGraph n) α)
    (x : Finset (Σ e : Edge n, LocalGroup e))
    (hoff : ∀ r ∈ x, r.1 ∉ (anchoredParents α).treeEdges) (hn : 1 ≤ n) :
    (SourceProgram.program.body.selection (atomInput b) p
      (tupleCode (List.ofFn (vertexCode b ∘ α)))).TransitiveAt (edgeState x) := by
  intro a ha d hd
  rw [selection_candidates p hp α hα x hn] at ha hd
  obtain ⟨r,hr,rfl⟩ := (mem_edgeState _ _).mp ha
  obtain ⟨t,ht,rfl⟩ := (mem_edgeState _ _).mp hd
  obtain ⟨g,hg,hgr⟩ := (anchoredParents α).grid_transitivity hn α hα x hoff r t hr ht
  refine ⟨g,?_,hgr⟩
  change g ∈ witnessPool localBound (atomInput b) True
    (program.body.cycleSet (atomInput b) p (tupleCode (List.ofFn (vertexCode b ∘ α)))) (edgeState x)
  exact witnessPool_mono localBound (atomInput b) True _ _ (edgeState x)
    (fundamentalPool_in_cycleSet p hp α hα x hn) hg

end QuotedGrid

end

end WitnessedSeparation.Grid

end


namespace WitnessedSeparation.Grid

noncomputable section

open Classical WitnessedChoice.TreeTest

variable {n : ℕ} {b : Vertex n → Scalar}

abbrev ConfigAtom (b : Vertex n → Scalar) := Σ v : Vertex n, Configuration b v

def configBlock (b : Vertex n → Scalar) (v : Vertex n) : Finset (ConfigAtom b) :=
  Finset.univ.image (Sigma.mk v)

lemma mem_configBlock (v : Vertex n) (a : ConfigAtom b) :
    a ∈ configBlock b v ↔ a.1 = v := by
  constructor
  · rintro ha
    obtain ⟨s,_,rfl⟩ := Finset.mem_image.mp ha
    rfl
  · intro h
    rcases a with ⟨w,a⟩
    dsimp at h
    subst w
    exact Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩

def atEdge (a : ConfigAtom b) (e : Edge n) (h : incident a.1 e) : LocalGroup e := a.2.state ⟨e,h⟩

namespace ParentEdges

variable {T : RootedTree (Vertex n)} (P : ParentEdges T)

def allowedConfig (x : Finset (Σ e : Edge n, LocalGroup e)) (a : ConfigAtom b) : Prop :=
  ∀ e, e ∉ P.treeEdges → ∀ h : incident a.1 e, Sigma.mk e (atEdge a e h) ∈ x

def configCompatibility (a c : ConfigAtom b) : Prop :=
  ∀ e ∈ P.treeEdges, ∀ ha : incident a.1 e, ∀ hc : incident c.1 e,
    atEdge a e ha = atEdge c e hc

def testProblem (x : Finset (Σ e : Edge n, LocalGroup e)) : Problem (Vertex n) (ConfigAtom b) where
  tree := T
  configs := Finset.univ
  block := configBlock b
  block_subset _ _ _ := Finset.mem_univ _
  block_unique v w a hv hw := (mem_configBlock v a).mp hv |>.symm.trans ((mem_configBlock w a).mp hw)
  allowed := P.allowedConfig x
  compatible _ _ := P.configCompatibility
  compatible_symm _ _ _ _ h e he ha hc := (h e he hc ha).symm

lemma solution_configs (x : Finset (Σ e : Edge n, LocalGroup e))
    (ht : ∃ t, (P.testProblem (b := b) x).Solution t) :
    ∃ t : (v : Vertex n) → Configuration b v,
      (∀ v, P.allowedConfig x ⟨v,t v⟩) ∧
      ∀ v w, T.Adj v w → P.configCompatibility ⟨v,t v⟩ ⟨w,t w⟩ := by
  obtain ⟨t,ht⟩ := ht
  have hv (v : Vertex n) : (t v).1 = v := (mem_configBlock v _).mp (ht.1 v).1
  let tt (v : Vertex n) : Configuration b v := (hv v) ▸ (t v).2
  have he (v : Vertex n) : (⟨v,tt v⟩ : ConfigAtom b) = t v := by
    have transport_pair {w : Vertex n} (a : Configuration b w) (h : w = v) :
        (⟨v,h ▸ a⟩ : ConfigAtom b) = ⟨w,a⟩ := by cases h; rfl
    exact transport_pair _ (hv v)
  refine ⟨tt,?_,?_⟩
  · intro v
    rw [he]
    exact (ht.1 v).2
  · intro v w hadj
    rw [he,he]
    exact ht.2 v w hadj

lemma exists_globals_of_solution (x : Finset (Σ e : Edge n, LocalGroup e))
    (hx : ∀ r ∈ x, ∀ s ∈ x, r.1 = s.1 → r = s)
    (ht : ∃ t, (P.testProblem (b := b) x).Solution t) :
    ∃ (s : (e : Edge n) → LocalGroup e) (t : (v : Vertex n) → Configuration b v),
      ∀ v (e : IncidentEdges v), (t v).state e = s e.val := by
  obtain ⟨t,hta,htc⟩ := P.solution_configs x ht
  let s (e : Edge n) := (t (head e)).state ⟨e,Or.inl rfl⟩
  refine ⟨s,t,?_⟩
  rintro v ⟨e,hi⟩
  rcases hi with hv | hv
  · subst v
    rfl
  · subst v
    by_cases he : e ∈ P.treeEdges
    · have ha : (edgeGraph P.treeEdges).Adj (tail e) (head e) :=
        ⟨e,he,Or.inl ⟨rfl,rfl⟩⟩
      exact htc _ _ ((P.graph_adj _ _).mp ha) e he (Or.inr rfl) (Or.inl rfl)
    · have h₁ := hta (tail e) e he (Or.inr rfl)
      have h₂ := hta (head e) e he (Or.inl rfl)
      have hh := hx _ h₁ _ h₂ rfl
      exact eq_of_heq (Sigma.mk.inj hh).2

lemma test_solution_of_zero (b : Vertex n → Scalar) (hb : ∑ v, b v = 0)
    (x : Finset (Σ e : Edge n, LocalGroup e)) (hx : ConsistentSelection x)
    (hoff : ∀ r ∈ x, r.1 ∉ P.treeEdges)
    (hcomplete : ∀ e, e ∉ P.treeEdges → ∃ r ∈ x, r.1 = e) :
    ∃ t, (P.testProblem (b := b) x).Solution t := by
  obtain ⟨s,t,hs,ht⟩ := extend_consistent_selection P b hb x hx hoff
  refine ⟨fun v => ⟨v,t v⟩,?_,?_⟩
  · intro v
    refine ⟨(mem_configBlock _ _).mpr rfl,?_⟩
    intro e he hi
    obtain ⟨⟨f,r⟩,hr,hfe⟩ := hcomplete e he
    dsimp at hfe
    subst f
    have hse := hs _ hr
    simpa only [atEdge,ht,hse] using hr
  · intro v w _ e he hv hw
    exact (ht v ⟨e,hv⟩).trans (ht w ⟨e,hw⟩).symm

lemma zero_of_test_solution (x : Finset (Σ e : Edge n, LocalGroup e))
    (hx : ∀ r ∈ x, ∀ s ∈ x, r.1 = s.1 → r = s)
    (ht : ∃ t, (P.testProblem (b := b) x).Solution t) : ∑ v, b v = 0 := by
  obtain ⟨s,t,ht⟩ := P.exists_globals_of_solution x hx ht
  exact total_charge_of_global_configurations b s t ht

theorem test_iff_zero (b : Vertex n → Scalar)
    (x : Finset (Σ e : Edge n, LocalGroup e)) (hx : ConsistentSelection x)
    (hoff : ∀ r ∈ x, r.1 ∉ P.treeEdges)
    (hcomplete : ∀ e, e ∉ P.treeEdges → ∃ r ∈ x, r.1 = e) :
    (∀ v, ((P.testProblem (b := b) x).survivors v).Nonempty) ↔ ∑ v, b v = 0 := by
  rw [(P.testProblem x).all_survive_iff_solution]
  exact ⟨P.zero_of_test_solution x hx.1,fun hb => P.test_solution_of_zero b hb x hx hoff hcomplete⟩

end ParentEdges

end





noncomputable section

open Classical WitnessedChoice WitnessedChoice.BGS WitnessedChoice.TreeTest Hereditary

variable {n : ℕ} {b : Vertex n → Scalar}

lemma atom_mem_state (a : Atom b) (s : Finset (Atom b)) : atom a ∈ elements (stateCode s) ↔ a ∈ s := by
  simp only [stateCode,elements_ofFinset,Finset.mem_image,atom_injective.eq_iff,exists_eq_right]

lemma chosen_incident_iff (x : Finset (Σ e : Edge n, LocalGroup e)) (v : Vertex n)
    (a : Configuration b v) (e : Edge n) (hi : incident v e) :
    (∃ z ∈ elements (stateCode (x.image Sum.inl : Finset (Atom b))) ∩ elements (edgeCode b e),
      inputHF (atomInput b) .I (atom (.inr ⟨v,a⟩)) z = true) ↔
      Sigma.mk e (a.state ⟨e,hi⟩) ∈ x := by
  simp only [Finset.mem_inter,stateCode,elements_ofFinset,Finset.image_image,
    Finset.mem_image,Function.comp_apply]
  constructor
  · rintro ⟨z,⟨⟨r,hr,rfl⟩,he⟩,hinc⟩
    have hre := (atom_mem_edgeCode _ _ _).mp he
    rcases r with ⟨f,s⟩
    dsimp at hre
    subst f
    obtain ⟨hi',hs⟩ := (input_inc_iff _ _ _ _).mp hinc
    rwa [hs]
  · intro h
    exact ⟨atom (.inl ⟨e,a.state ⟨e,hi⟩⟩),⟨⟨⟨e,a.state ⟨e,hi⟩⟩,h,rfl⟩,
      (atom_mem_edgeCode _ _ _).mpr rfl⟩,(input_inc_iff _ _ _ _).mpr ⟨hi,rfl⟩⟩

namespace QuotedGrid

open QuotedTerm QuotedFormula SourceSyntax

variable {k : ℕ}

lemma meaning_edgeDiff (env : Fin k → HF (Atom b)) (E T : QuotedTerm k) (D : Finset (Edge n))
    (hE : E.meaning (atomInput b) env = ofFinset (Finset.univ.image (edgeCode b)))
    (hT : T.meaning (atomInput b) env = ofFinset (D.image (edgeCode b))) :
    (E.diff T).meaning (atomInput b) env = ofFinset ((Finset.univ \ D).image (edgeCode b)) := by
  simp only [meaning_diff,hE,hT,elements_ofFinset]
  apply ofFinset_inj.mpr
  ext z
  simp only [Finset.mem_filter,Finset.mem_image,Finset.mem_univ,true_and,Finset.mem_sdiff,
    not_exists,not_and]
  constructor
  · rintro ⟨⟨e,rfl⟩,he⟩
    exact ⟨e,fun ht => he e ht rfl,rfl⟩
  · rintro ⟨e,he,rfl⟩
    exact ⟨⟨e,rfl⟩,fun f hf hfe => he ((edgeCode_injective hfe) ▸ hf)⟩

lemma meaning_allowed {T₀ : RootedTree (Vertex n)} (env : Fin k → HF (Atom b))
    (E T xt vt at₀ : QuotedTerm k) (P : ParentEdges T₀)
    (x : Finset (Σ e : Edge n, LocalGroup e)) (v : Vertex n) (a : Configuration b v)
    (hE : E.meaning (atomInput b) env = ofFinset (Finset.univ.image (edgeCode b)))
    (hT : T.meaning (atomInput b) env = ofFinset (P.treeEdges.image (edgeCode b)))
    (hx : xt.meaning (atomInput b) env = stateCode (x.image Sum.inl))
    (hv : vt.meaning (atomInput b) env = vertexCode b v)
    (ha : at₀.meaning (atomInput b) env = atom (.inr ⟨v,a⟩)) (hn : 1 ≤ n) :
    (allowed E T xt vt at₀).meaning (atomInput b) env ↔ P.allowedConfig x ⟨v,a⟩ := by
  have hd := meaning_edgeDiff env E T P.treeEdges hE hT
  have hi (e : Edge n) := meaning_incident (Fin.cons (edgeCode b e) env) vt.up (var 0) v e hv rfl hn
  simp only [allowed,meaning_allIn,hd,elements_ofFinset,Finset.forall_mem_image,
    Finset.mem_sdiff,Finset.mem_univ,true_and,meaning_imp,hi,meaning_existsIn,meaning_inter,
    QuotedTerm.meaning_up,hx,meaning_var,Fin.cons_zero,meaning_input,ha]
  constructor
  · intro h e he hi
    exact (chosen_incident_iff x v a e hi).mp (h he hi)
  · intro h e he hi
    exact (chosen_incident_iff x v a e hi).mpr (h e he hi)

end QuotedGrid

end





noncomputable section

open Classical WitnessedChoice WitnessedChoice.BGS WitnessedChoice.TreeTest Hereditary

variable {n : ℕ} {b : Vertex n → Scalar}

lemma common_edge_unique (e f : Edge n) (v w : Vertex n) (hvw : v ≠ w)
    (he : incident v e) (he' : incident w e) (hf : incident v f) (hf' : incident w f) : e=f := by
  have heq := (endpoints_incident_iff e v w).mpr ⟨hvw,he,he'⟩
  have hfq := (endpoints_incident_iff f v w).mpr ⟨hvw,hf,hf'⟩
  apply edge_eq_of_endpoints
  rcases heq with ⟨h₁,h₂⟩ | ⟨h₂,h₁⟩ <;> rcases hfq with ⟨h₃,h₄⟩ | ⟨h₄,h₃⟩
  · exact Or.inl ⟨h₁.symm.trans h₃,h₂.symm.trans h₄⟩
  · exact Or.inr ⟨h₁.symm.trans h₃,h₂.symm.trans h₄⟩
  · exact Or.inr ⟨h₂.symm.trans h₄,h₁.symm.trans h₃⟩
  · exact Or.inl ⟨h₂.symm.trans h₄,h₁.symm.trans h₃⟩

lemma atom_config_mem (a : ConfigAtom b) (s : Finset (ConfigAtom b)) :
    atom (.inr a) ∈ elements (stateCode (s.image Sum.inr : Finset (Atom b))) ↔ a ∈ s := by
  rw [atom_mem_state]
  simp only [Finset.mem_image,Sum.inr.injEq,exists_eq_right]

namespace ParentEdges

variable {T₀ : RootedTree (Vertex n)} (P : ParentEdges T₀)

lemma compatible_edge_iff (v w : Vertex n) (a : Configuration b v) (c : Configuration b w)
    (e : Edge n) (he : e ∈ P.treeEdges) (hne : v ≠ w) (hv : incident v e) (hw : incident w e) :
    P.configCompatibility ⟨v,a⟩ ⟨w,c⟩ ↔ a.state ⟨e,hv⟩ = c.state ⟨e,hw⟩ := by
  constructor
  · exact fun h => h e he hv hw
  · intro h f _ hf hg
    have heq := common_edge_unique e f v w hne hv hw hf hg
    subst f
    exact h

end ParentEdges

namespace QuotedGrid

open QuotedTerm QuotedFormula SourceSyntax

variable {k : ℕ}

lemma meaning_support (env : Fin k → HF (Atom b)) (wt St et at₀ : QuotedTerm k)
    (s : Finset (ConfigAtom b)) (v w : Vertex n) (a : Configuration b v) (e : Edge n)
    (hv : incident v e) (hw : incident w e)
    (hW : wt.meaning (atomInput b) env = vertexCode b w)
    (hS : St.meaning (atomInput b) env = stateCode (s.image Sum.inr))
    (hE : et.meaning (atomInput b) env = edgeCode b e)
    (hA : at₀.meaning (atomInput b) env = atom (.inr ⟨v,a⟩)) :
    (existsIn (wt.diff St) (existsIn et.up
      ((input .I at₀.up.up (var 0)).and (input .I (var 1) (var 0))))).meaning (atomInput b) env ↔
      ∃ c : Configuration b w, Sigma.mk w c ∉ s ∧ a.state ⟨e,hv⟩ = c.state ⟨e,hw⟩ := by
  simp only [meaning_existsIn,meaning_diff,hW,elements_ofFinset,Finset.mem_filter,and_assoc,
    exists_vertexCode,QuotedTerm.meaning_up,hS,atom_config_mem,hE,WitnessedSeparation.Grid.exists_edgeCode,
    meaning_and,meaning_input,hA,meaning_var,Fin.cons_zero,Fin.cons_one,input_inc_iff]
  constructor
  · rintro ⟨c,hc,r,⟨hv',h₁⟩,⟨hw',h₂⟩⟩
    exact ⟨c,hc,h₁.trans h₂.symm⟩
  · rintro ⟨c,hc,h⟩
    exact ⟨c,hc,a.state ⟨e,hv⟩,⟨hv,rfl⟩,⟨hw,h.symm⟩⟩

lemma meaning_unsupported {T₀ : RootedTree (Vertex n)} (env : Fin k → HF (Atom b))
    (V T St vt at₀ : QuotedTerm k) (P : ParentEdges T₀) (s : Finset (ConfigAtom b))
    (v : Vertex n) (a : Configuration b v)
    (hV : V.meaning (atomInput b) env = ofFinset (Finset.univ.image (vertexCode b)))
    (hT : T.meaning (atomInput b) env = ofFinset (P.treeEdges.image (edgeCode b)))
    (hS : St.meaning (atomInput b) env = stateCode (s.image Sum.inr))
    (hv : vt.meaning (atomInput b) env = vertexCode b v)
    (ha : at₀.meaning (atomInput b) env = atom (.inr ⟨v,a⟩)) (hn : 1 ≤ n) :
    (unsupported V T St vt at₀).meaning (atomInput b) env ↔
      ∃ w, T₀.Adj v w ∧ ¬ ∃ c ∈ configBlock b w, c ∉ s ∧ P.configCompatibility ⟨v,a⟩ c := by
  have hi (e : Edge n) (w : Vertex n) := meaning_incident
    (Fin.cons (vertexCode b w) (Fin.cons (edgeCode b e) env)) vt.up.up (var 1) v e hv rfl hn
  have hi' (e : Edge n) (w : Vertex n) := meaning_incident
    (Fin.cons (vertexCode b w) (Fin.cons (edgeCode b e) env)) (var 0) (var 1) w e rfl rfl hn
  simp only [unsupported,meaning_existsIn,hT,elements_ofFinset,Finset.mem_image,
    exists_exists_and_eq_and,QuotedTerm.meaning_up,hV,Finset.mem_univ,true_and,
    exists_exists_eq_and,meaning_allList,List.mem_cons,List.not_mem_nil,forall_eq_or_imp,forall_false,implies_true,and_true,
    meaning_neg,meaning_eq,meaning_var,Fin.cons_zero,hv,(vertexCode_injective hn).eq_iff,hi,hi']
  constructor
  · rintro ⟨e,he,w,hvw,hve,hwe,hsup⟩
    have hne : v ≠ w := Ne.symm hvw
    have hAdj : T₀.Adj v w := (P.graph_adj _ _).mp
      ⟨e,he,(endpoints_incident_iff e v w).mpr ⟨hne,hve,hwe⟩⟩
    refine ⟨w,hAdj,?_⟩
    rintro ⟨⟨u,c⟩,hc,hcs,hcomp⟩
    have hu := (mem_configBlock w ⟨u,c⟩).mp hc
    dsimp at hu
    subst u
    apply hsup
    apply (meaning_support (Fin.cons (vertexCode b w) (Fin.cons (edgeCode b e) env))
      (var 0) St.up.up (var 1) at₀.up.up s v w a e hve hwe rfl hS rfl ha).mpr
    exact ⟨c,hcs,(P.compatible_edge_iff v w a c e he hne hve hwe).mp hcomp⟩
  · rintro ⟨w,hadj,hsup⟩
    obtain ⟨e,he,hep⟩ := (P.graph_adj _ _).mpr hadj
    obtain ⟨hne,hve,hwe⟩ := (endpoints_incident_iff e v w).mp hep
    refine ⟨e,he,w,Ne.symm hne,hve,hwe,?_⟩
    intro hh
    obtain ⟨c,hcs,hce⟩ := (meaning_support
      (Fin.cons (vertexCode b w) (Fin.cons (edgeCode b e) env))
      (var 0) St.up.up (var 1) at₀.up.up s v w a e hve hwe rfl hS rfl ha).mp hh
    exact hsup ⟨⟨w,c⟩,(mem_configBlock _ _).mpr rfl,hcs,
      (P.compatible_edge_iff v w a c e he hne hve hwe).mpr hce⟩

end QuotedGrid

end





noncomputable section

open Classical WitnessedChoice WitnessedChoice.BGS WitnessedChoice.TreeTest Hereditary

variable {n : ℕ} {b : Vertex n → Scalar}

lemma configAtoms_grid : WitnessedChoice.configAtoms (atomInput b) =
    (Finset.univ : Finset (ConfigAtom b)).image Sum.inr := by
  ext a
  simp only [WitnessedChoice.configAtoms,Finset.mem_filter,Finset.mem_univ,true_and,
    atomInput,decide_eq_true_eq,Finset.mem_image]
  constructor
  · intro h
    cases h with | cf v c => exact ⟨⟨v,c⟩,rfl⟩
  · rintro ⟨⟨v,c⟩,rfl⟩
    exact .cf v c

lemma config_mem_vertexCode (a : ConfigAtom b) (v : Vertex n) :
    atom (.inr a) ∈ elements (vertexCode b v) ↔ a.1 = v := by
  rw [mem_vertexCode_iff]
  constructor
  · rintro ⟨c,hc⟩
    exact congrArg Sigma.fst (Sum.inr.inj (atom_injective hc))
  · intro h
    rcases a with ⟨w,c⟩
    dsimp at h
    subst w
    exact ⟨c,rfl⟩

namespace QuotedGrid

open QuotedTerm QuotedFormula SourceSyntax

variable {k : ℕ}

lemma meaning_deletedStep {T₀ : RootedTree (Vertex n)} (env : Fin k → HF (Atom b))
    (V E T xt St : QuotedTerm k) (P : ParentEdges T₀) (s : Finset (ConfigAtom b))
    (x : Finset (Σ e : Edge n, LocalGroup e))
    (hV : V.meaning (atomInput b) env = ofFinset (Finset.univ.image (vertexCode b)))
    (hE : E.meaning (atomInput b) env = ofFinset (Finset.univ.image (edgeCode b)))
    (hT : T.meaning (atomInput b) env = ofFinset (P.treeEdges.image (edgeCode b)))
    (hx : xt.meaning (atomInput b) env = stateCode (x.image Sum.inl))
    (hS : St.meaning (atomInput b) env = stateCode (s.image Sum.inr)) (hn : 1 ≤ n) :
    (deletedStep V E T xt St).meaning (atomInput b) env =
      stateCode (((P.testProblem x).update s).image Sum.inr) := by
  have hp (v : Vertex n) (a : Configuration b v) :
      (existsIn V.up ((mem (var 1) (var 0)).and
        ((allowed E.up.up T.up.up xt.up.up (var 0) (var 1)).neg.or
          (unsupported V.up.up T.up.up St.up.up (var 0) (var 1))))).meaning (atomInput b)
        (Fin.cons (atom (.inr ⟨v,a⟩)) env) ↔
      ¬ P.allowedConfig x ⟨v,a⟩ ∨ ∃ w, T₀.Adj v w ∧
        ¬ ∃ c ∈ configBlock b w, c ∉ s ∧ P.configCompatibility ⟨v,a⟩ c := by
    have hex (Q : Vertex n → Prop) : (∃ w, v=w ∧ Q w) ↔ Q v := by
      constructor
      · rintro ⟨w,rfl,h⟩
        exact h
      · exact fun h => ⟨v,rfl,h⟩
    simp only [meaning_existsIn,QuotedTerm.meaning_up,hV,elements_ofFinset,Finset.mem_image,
      Finset.mem_univ,true_and,exists_exists_eq_and,meaning_and,meaning_mem,meaning_var,
      Fin.cons_zero,Fin.cons_one,config_mem_vertexCode,hex,
      meaning_or,meaning_neg]
    rw [meaning_allowed (Fin.cons (vertexCode b v) (Fin.cons (atom (.inr ⟨v,a⟩)) env))
      E.up.up T.up.up xt.up.up (var 0) (var 1) P x v a hE hT hx rfl rfl hn,
      meaning_unsupported (Fin.cons (vertexCode b v) (Fin.cons (atom (.inr ⟨v,a⟩)) env))
      V.up.up T.up.up St.up.up (var 0) (var 1) P s v a hV hT hS rfl rfl hn]
  simp only [deletedStep,meaning_cup,hS,QuotedTerm.meaning_filter,meaning_configAtoms,configAtoms_grid,
    stateCode,elements_ofFinset,Finset.image_image]
  apply ofFinset_inj.mpr
  ext z
  simp only [Finset.mem_union,Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and,
    Problem.update,ParentEdges.testProblem,Finset.mem_union,Finset.mem_filter,Finset.mem_univ,
    true_and,mem_configBlock]
  constructor
  · rintro (⟨a,ha,rfl⟩ | ⟨⟨⟨v,a⟩,rfl⟩,h⟩)
    · exact ⟨a,Or.inl ha,rfl⟩
    · refine ⟨⟨v,a⟩,Or.inr ?_,rfl⟩
      rcases (hp v a).mp h with h | ⟨w,hw,hno⟩
      · exact Or.inl h
      · exact Or.inr ⟨v,rfl,w,hw,by simpa only [mem_configBlock] using hno⟩
  · rintro ⟨⟨v,a⟩,(ha | ha),rfl⟩
    · exact Or.inl ⟨⟨v,a⟩,ha,rfl⟩
    · refine Or.inr ⟨⟨⟨v,a⟩,rfl⟩,(hp v a).mpr ?_⟩
      rcases ha with h | ⟨w,hw,u,hu,hno⟩
      · exact Or.inl h
      · dsimp at hw
        subst w
        exact Or.inr ⟨u,hu,by simpa only [mem_configBlock] using hno⟩

end QuotedGrid

end

end WitnessedSeparation.Grid


section

namespace WitnessedChoice.TreeTest.Problem

open WitnessedChoice.BGS

variable {V A : Type} (P : Problem V A)

lemma run_eq_finite (k : ℕ) : P.run k = FiniteIteration.run P.update k := by
  induction k with
  | zero => rfl
  | succ k ih => exact congrArg P.update ih

end WitnessedChoice.TreeTest.Problem

namespace WitnessedSeparation.Grid

noncomputable section

open Classical WitnessedChoice WitnessedChoice.BGS WitnessedChoice.TreeTest Hereditary

variable {n : ℕ} {b : Vertex n → Scalar}

namespace QuotedGrid

open QuotedTerm QuotedFormula SourceSyntax

variable {k : ℕ}

lemma value_deletion {T₀ : RootedTree (Vertex n)} (env : Fin k → HF (Atom b))
    (V E T xt : QuotedTerm k) (P : ParentEdges T₀)
    (x : Finset (Σ e : Edge n, LocalGroup e)) (p : Polynomial ℝ) (hp : GridResources p b)
    (hV : V.meaning (atomInput b) env = ofFinset (Finset.univ.image (vertexCode b)))
    (hE : E.meaning (atomInput b) env = ofFinset (Finset.univ.image (edgeCode b)))
    (hT : T.meaning (atomInput b) env = ofFinset (P.treeEdges.image (edgeCode b)))
    (hx : xt.meaning (atomInput b) env = stateCode (x.image Sum.inl)) (hn : 1 ≤ n) :
    (CPTTerm.quoted (deletedStep V.up E.up T.up xt.up (var 0))).iterate.value (atomInput b) p env =
      stateCode ((P.testProblem x).deleted.image Sum.inr) := by
  have hc : Fintype.card (ConfigAtom b) ≤ Fintype.card (Atom b) := by
    exact Fintype.card_le_of_injective (fun c : ConfigAtom b => (Sum.inr c : Atom b)) Sum.inr_injective
  have htime : Fintype.card (ConfigAtom b) ≤ resource p (Fintype.card (Atom b)) := by
    have := hp.basic
    omega
  have hspace : (TC (ofFinset ((Finset.univ : Finset (ConfigAtom b)).image
      (fun a => atom (Sum.inr a : Atom b))))).card ≤ resource p (Fintype.card (Atom b)) := by
    have he : ofFinset ((Finset.univ : Finset (ConfigAtom b)).image (fun a => atom (Sum.inr a : Atom b))) =
        stateCode ((Finset.univ : Finset (ConfigAtom b)).image Sum.inr) := by
      simp only [stateCode,Finset.image_image,Function.comp_def]
    rw [he,TC_stateCode,Finset.card_image_of_injective _ atom_injective,
      Finset.card_image_of_injective _ Sum.inr_injective,Finset.card_univ]
    exact htime
  apply CPTTerm.value_eq
  rw [CPTTerm.eval_iterate]
  have h := ordinaryIteration_encoded (resource p (Fintype.card (Atom b)))
    (fun a : ConfigAtom b => atom (Sum.inr a : Atom b)) (P.testProblem x).update
    (fun s => (deletedStep V.up E.up T.up xt.up (var 0)).meaning (atomInput b) (Fin.cons s env))
    (fun s => some ((CPTTerm.quoted (deletedStep V.up E.up T.up xt.up (var 0))).value
      (atomInput b) p (Fin.cons s env)))
    (by intro s; rw [CPTTerm.value_quoted])
    (by
      intro s
      have hcode (s : Finset (ConfigAtom b)) : ofFinset (s.image (fun a => atom (Sum.inr a : Atom b))) =
          stateCode (s.image Sum.inr) := by simp only [stateCode,Finset.image_image,Function.comp_def]
      rw [hcode,hcode]
      exact meaning_deletedStep (Fin.cons (stateCode (s.image Sum.inr)) env)
        V.up E.up T.up xt.up (var 0) P s x hV hE hT hx rfl hn)
    (P.testProblem x).le_update htime hspace
  convert h using 2
  simp only [stateCode,Finset.image_image,Function.comp_def,Problem.deleted,
    ParentEdges.testProblem,Finset.card_univ,Problem.run_eq_finite]

end QuotedGrid

end

end WitnessedSeparation.Grid

end


namespace WitnessedSeparation.Grid

noncomputable section

open Classical WitnessedChoice WitnessedChoice.BGS WitnessedChoice.TreeTest Hereditary

variable {n : ℕ} {b : Vertex n → Scalar}

lemma selected_inter_singleton (x : Finset (Σ e : Edge n, LocalGroup e))
    (hx : ∀ r ∈ x, ∀ t ∈ x, r.1=t.1 → r=t) (r : Σ e : Edge n, LocalGroup e) (hr : r ∈ x) :
    elements (stateCode (x.image Sum.inl : Finset (Atom b))) ∩ elements (edgeCode b r.1) =
      {atom (.inl r)} := by
  ext z
  simp only [Finset.mem_inter,stateCode,elements_ofFinset,Finset.image_image,
    Finset.mem_image,Function.comp_apply,Finset.mem_singleton]
  constructor
  · rintro ⟨⟨t,ht,rfl⟩,he⟩
    have heq := (atom_mem_edgeCode _ _ _).mp he
    rw [hx t ht r hr heq]
  · rintro rfl
    exact ⟨⟨r,hr,rfl⟩,(atom_mem_edgeCode _ _ _).mpr rfl⟩

lemma edgeState_subset_edgeAtoms (x : Finset (Σ e : Edge n, LocalGroup e)) :
    edgeState (b := b) x ⊆ WitnessedChoice.edgeAtoms (atomInput b) := by
  rw [edgeAtoms_grid]
  exact Finset.image_subset_image (Finset.subset_univ _)

namespace QuotedGrid

open QuotedTerm QuotedFormula SourceSyntax

variable {k : ℕ}

lemma meaning_complete {T₀ : RootedTree (Vertex n)} (env : Fin k → HF (Atom b))
    (E T xt : QuotedTerm k) (P : ParentEdges T₀)
    (x : Finset (Σ e : Edge n, LocalGroup e)) (hx : ConsistentSelection x)
    (hoff : ∀ r ∈ x, r.1 ∉ P.treeEdges)
    (hc : ∀ e, e ∉ P.treeEdges → ∃ r ∈ x, r.1=e)
    (hE : E.meaning (atomInput b) env = ofFinset (Finset.univ.image (edgeCode b)))
    (hT : T.meaning (atomInput b) env = ofFinset (P.treeEdges.image (edgeCode b)))
    (hX : xt.meaning (atomInput b) env = stateCode (x.image Sum.inl)) :
    (complete E T xt).meaning (atomInput b) env := by
  have hfirst : (eq xt (xt.inter QuotedTerm.edgeAtoms)).meaning (atomInput b) env := by
    simp only [meaning_eq,meaning_inter,hX,meaning_edgeAtoms,stateCode,elements_ofFinset]
    congr 1
    exact (Finset.inter_eq_left.mpr (Finset.image_subset_image (edgeState_subset_edgeAtoms x))).symm
  have hone : (allIn (E.diff T) (eq (xt.up.inter (var 0)).card (nat 1))).meaning (atomInput b) env := by
    simp only [meaning_allIn,meaning_edgeDiff env E T P.treeEdges hE hT,elements_ofFinset,
      Finset.forall_mem_image,Finset.mem_sdiff,Finset.mem_univ,true_and]
    intro e he
    obtain ⟨r,hr,hre⟩ := hc e he
    simp only [meaning_eq,meaning_card,meaning_inter,QuotedTerm.meaning_up,hX,meaning_var,
      Fin.cons_zero,meaning_nat,cardHF,elements_ofFinset]
    rw [←hre,selected_inter_singleton x hx.1 r hr,Finset.card_singleton]
  have hzero : (allIn T (eq (xt.up.inter (var 0)) empty)).meaning (atomInput b) env := by
    simp only [meaning_allIn,hT,elements_ofFinset,Finset.forall_mem_image,meaning_eq,
      meaning_inter,QuotedTerm.meaning_up,hX,meaning_var,Fin.cons_zero,meaning_empty]
    intro e he
    apply (selected_inter_empty x e).mpr
    intro r hr hh
    exact hoff r hr (hh.symm ▸ he)
  simpa only [complete,meaning_allList,List.mem_cons,List.not_mem_nil,forall_eq_or_imp,
    forall_false,implies_true,and_true] using ⟨hfirst,hone,hzero⟩

lemma meaning_survives (env : Fin k → HF (Atom b)) (V D : QuotedTerm k)
    (s : Finset (ConfigAtom b))
    (hV : V.meaning (atomInput b) env = ofFinset (Finset.univ.image (vertexCode b)))
    (hD : D.meaning (atomInput b) env = stateCode (s.image Sum.inr)) :
    (allIn V (nonempty ((var 0).diff D.up))).meaning (atomInput b) env ↔
      ∀ v, ((configBlock b v).filter (· ∉ s)).Nonempty := by
  simp only [meaning_allIn,hV,elements_ofFinset,Finset.forall_mem_image,Finset.mem_univ,
    forall_const,nonempty,meaning_neg,meaning_eq,meaning_diff,meaning_var,Fin.cons_zero,
    QuotedTerm.meaning_up,hD,meaning_empty]
  apply forall_congr'
  intro v
  rw [show (emptyHF : HF (Atom b)) = ofFinset ∅ from rfl,ofFinset_inj]
  change ({z ∈ elements (vertexCode b v) | z ∉ elements (stateCode (s.image Sum.inr))} : Finset _) ≠ ∅ ↔ _
  rw [←Finset.nonempty_iff_ne_empty]
  constructor
  · rintro ⟨z,hz⟩
    obtain ⟨hz,hnot⟩ := Finset.mem_filter.mp hz
    obtain ⟨c,rfl⟩ := (mem_vertexCode_iff v z).mp hz
    exact ⟨⟨v,c⟩,Finset.mem_filter.mpr ⟨(mem_configBlock _ _).mpr rfl,
      fun h => hnot ((atom_config_mem _ _).mpr h)⟩⟩
  · rintro ⟨⟨w,c⟩,hc⟩
    obtain ⟨hc,hn⟩ := Finset.mem_filter.mp hc
    have hw := (mem_configBlock v ⟨w,c⟩).mp hc
    dsimp at hw
    subst w
    exact ⟨atom (.inr ⟨v,c⟩),Finset.mem_filter.mpr ⟨(mem_vertexCode_iff _ _).mpr ⟨c,rfl⟩,
      fun h => hn ((atom_config_mem _ _).mp h)⟩⟩

end QuotedGrid

end





noncomputable section

open Classical WitnessedChoice WitnessedChoice.BGS WitnessedChoice.TreeTest Hereditary

variable {n : ℕ} {b : Vertex n → Scalar}

lemma testProblem_block {T₀ : RootedTree (Vertex n)} (P : ParentEdges T₀)
    (x : Finset (Σ e : Edge n, LocalGroup e)) (v : Vertex n) :
    (P.testProblem (b := b) x).block v = configBlock b v := rfl

lemma survivors_test_iff_zero {T₀ : RootedTree (Vertex n)} (P : ParentEdges T₀)
    (x : Finset (Σ e : Edge n, LocalGroup e)) (hx : ConsistentSelection x)
    (hoff : ∀ r ∈ x, r.1 ∉ P.treeEdges)
    (hc : ∀ e, e ∉ P.treeEdges → ∃ r ∈ x, r.1=e) :
    (∀ v, ((configBlock b v).filter (· ∉ (P.testProblem (b := b) x).deleted)).Nonempty) ↔
      ∑ v, b v = 0 := by
  have h := P.test_iff_zero b x hx hoff hc
  have hs (v : Vertex n) : (P.testProblem (b := b) x).survivors v =
      (configBlock b v).filter (· ∉ (P.testProblem (b := b) x).deleted) := by
    ext a
    simp only [Problem.survivors,Finset.mem_filter,testProblem_block]
  simpa only [hs] using h

namespace QuotedGrid

open QuotedTerm QuotedFormula SourceSyntax SourceProgram

attribute [local irreducible] QuotedTerm.tree SourceSyntax.complete SourceSyntax.deletedStep

lemma value_output (p : Polynomial ℝ) (hp : GridResources p b)
    (α : Fin 4 → Vertex n) (hα : AnchoredTree.Resolving (boxGraph n) α)
    (x : Finset (Σ e : Edge n, LocalGroup e)) (hx : ConsistentSelection x)
    (hoff : ∀ r ∈ x, r.1 ∉ (anchoredParents α).treeEdges)
    (hc : ∀ e, e ∉ (anchoredParents α).treeEdges → ∃ r ∈ x, r.1=e) (hn : 1 ≤ n) :
    SourceProgram.output.value (atomInput b) p
      (Fin.cons (stateCode (edgeState x)) (Fin.cons (tupleCode (List.ofFn (vertexCode b ∘ α))) Fin.elim0)) =
      decide (∑ v, b v = 0) := by
  let R := distancesCode b (boxGraph n)
  let T := ofFinset ((anchoredParents α).treeEdges.image (edgeCode b))
  let D : HF (Atom b) := stateCode (((anchoredParents α).testProblem (b := b) x).deleted.image Sum.inr)
  let env₀ : Fin 3 → HF (Atom b) := Fin.cons R
    (Fin.cons (stateCode (edgeState x)) (Fin.cons (tupleCode (List.ofFn (vertexCode b ∘ α))) Fin.elim0))
  let env₁ : Fin 4 → HF (Atom b) := Fin.cons T env₀
  let env₂ : Fin 5 → HF (Atom b) := Fin.cons D env₁
  have ht : (tree (var 2) QuotedTerm.vertexBlocks QuotedTerm.edgeBlocks (var 0)).meaning
      (atomInput b) env₀ = T :=
    meaning_tree env₀ (var 2) _ _ (var 0) α hα rfl
      (quoted_vertexBlocks hn env₀) (quoted_edgeBlocks env₀) rfl hn
  have hd : (CPTTerm.quoted
      (deletedStep QuotedTerm.vertexBlocks QuotedTerm.edgeBlocks (var 1) (var 3) (var 0))).iterate.value
        (atomInput b) p env₁ = D := by
    exact value_deletion env₁ QuotedTerm.vertexBlocks QuotedTerm.edgeBlocks (var 0) (var 2)
      (anchoredParents α) x p hp (quoted_vertexBlocks hn env₁) (quoted_edgeBlocks env₁) rfl rfl hn
  have hcomplete := meaning_complete env₂ QuotedTerm.edgeBlocks (var 1) (var 3)
    (anchoredParents α) x hx hoff hc (quoted_edgeBlocks env₂) rfl rfl
  have hsurvive := meaning_survives env₂ QuotedTerm.vertexBlocks (var 0)
    ((anchoredParents α).testProblem (b := b) x).deleted (quoted_vertexBlocks hn env₂) rfl
  have hm : ((complete QuotedTerm.edgeBlocks (var 1) (var 3)).and
      (allIn QuotedTerm.vertexBlocks (nonempty ((var 0).diff (var 1))))).meaning (atomInput b) env₂ ↔
        ∑ v, b v = 0 := by
    rw [meaning_and,and_iff_right hcomplete]
    change (allIn QuotedTerm.vertexBlocks (nonempty ((var 0).diff (var 1)))).meaning
      (atomInput b) env₂ ↔ _ at hsurvive
    exact hsurvive.trans (survivors_test_iff_zero (b := b) (anchoredParents α) x hx hoff hc)
  rw [SourceProgram.output,CPTFormula.value_letIn,value_distances _ p hp hn,
    CPTFormula.value_letIn,CPTTerm.value_quoted]
  change (CPTFormula.letIn _ _).value (atomInput b) p
    (Fin.cons ((tree (var 2) QuotedTerm.vertexBlocks QuotedTerm.edgeBlocks (var 0)).meaning
      (atomInput b) env₀) env₀) = _
  rw [ht,CPTFormula.value_letIn]
  change (CPTFormula.quoted _).value (atomInput b) p
    (Fin.cons ((CPTTerm.quoted
      (deletedStep QuotedTerm.vertexBlocks QuotedTerm.edgeBlocks (var 1) (var 3) (var 0))).iterate.value
        (atomInput b) p env₁) env₁) = _
  rw [hd,CPTFormula.value_quoted]
  apply Bool.eq_iff_iff.mpr
  simpa only [decide_eq_true_eq] using hm

end QuotedGrid

end

end WitnessedSeparation.Grid



namespace WitnessedChoice.BGS

noncomputable section

open Classical WitnessedSeparation WitnessedSeparation.Hereditary

namespace Realizes

variable {A : Type} [Fintype A] {P : Selection A}
    {step : HF A → HF A → Result (HF A)} {choice : HF A → Result (HF A)}
    {witness : HF A → HF A → Result (HF A)}
    (hr : Realizes P step choice witness)

include hr

lemma first_encode {b : ℕ → Finset A} {c : ℕ → Option A} {t : ℕ}
    (hb : P.FirstStabilization b c t) :
    FirstPath step choice (stateCode ∘ b) (choiceCode ∘ c) t := by
  refine ⟨⟨?_,?_⟩,?_,?_⟩
  · simp only [Function.comp_apply,hb.1.1,stateCode,Finset.image_empty]
    rfl
  · intro i hi
    obtain ⟨hc,hs⟩ := hb.1.2 i hi
    refine ⟨⟨ofFinset ((P.choices (b i)).image choiceCode),hr.choice_eq _,?_⟩,?_⟩
    · exact (elements_ofFinset _ ▸ Finset.mem_image.mpr ⟨c i,hc,rfl⟩)
    · simpa only [Function.comp_apply,hs] using hr.step_eq (b i) (c i) hc
  · intro i hi he
    exact hb.2.1 i hi (stateCode_inj.mp he)
  · exact congrArg stateCode hb.2.2

lemma value_constant {S : Input A} {α : HF A} (hf : P.Filtered S α)
    (p : ℕ) (hp : Fintype.card A+2 ≤ p) (free : Finset (Fin 1))
    (output : HF A → Result Bool) (hout : ∀ x : Finset A, (output (stateCode x)).isSome)
    (v : Bool)
    (ht : ∀ b c t, P.FirstStabilization b c t → output (stateCode (b t)) = some v) :
    witnessedIteration S p free (Fin.cons α Fin.elim0) step choice witness output = some v := by
  have ht' : ∀ b c t, FirstPath step choice b c t → output (b t) = some v := by
    intro b c t hh
    obtain ⟨_,hb,_⟩ := hr.prefix_decode hh.1
    rw [hb t (by omega)]
    exact ht _ _ t (hr.first_decode hh)
  have hiff : (∀ b c t, FirstPath step choice b c t → output (b t) = some true) ↔ v = true := by
    constructor
    · intro h
      obtain ⟨b,c,t,hb⟩ := P.exists_path
      have h₁ := h _ _ t (hr.first_encode hb)
      have h₂ := ht' _ _ t (hr.first_encode hb)
      exact Option.some.inj (h₂.symm.trans h₁)
    · intro hv b c t hh
      exact (ht' b c t hh).trans (congrArg some hv)
  unfold witnessedIteration
  rw [ite_eq_left (hr.good hf p hp free output hout)]
  rw [propext hiff]
  cases v <;> simp

end Realizes

namespace GuardedProgram

open WitnessedChoice.RelationPools

lemma value_constant {A : Type} [Fintype A] (G : GuardedProgram) (S : Input A) (p : Polynomial ℝ)
    (α₀ : Fin 4 → Finset A) (hα : ∀ i, α₀ i ∈ blocks S)
    (hp : Fintype.card A+2 ≤ resource p (Fintype.card A)) (v : Bool)
    (ht : ∀ B c t, (G.selection S p (parameterCode α₀)).FirstStabilization B c t →
      G.output.value S p (Fin.cons (stateCode (B t)) (Fin.cons (parameterCode α₀) Fin.elim0)) = v) :
    G.formula.eval S p (Fin.cons (parameterCode α₀) Fin.elim0) = some v := by
  apply (G.realizes S p (parameterCode α₀)).value_constant
    (guardedSelection_filtered G.localBound S True _ _ α₀ hα)
    (resource p (Fintype.card A)) hp
  · intro x
    rw [G.output.eval_value]
    simp
  · intro B c t h
    rw [G.output.eval_value,ht B c t h]

end GuardedProgram

end

end WitnessedChoice.BGS



namespace WitnessedSeparation.Grid

noncomputable section

open Classical WitnessedChoice WitnessedChoice.BGS Hereditary RelationPools

variable {n : ℕ} {b : Vertex n → Scalar}

namespace QuotedGrid

open SourceProgram

attribute [local irreducible] SourceProgram.candidates SourceProgram.cycles SourceProgram.output

lemma terminal_output (p : Polynomial ℝ) (hp : GridResources p b)
    (α : Fin 4 → Vertex n) (hα : AnchoredTree.Resolving (boxGraph n) α) (hn : 1 ≤ n)
    (B : ℕ → Finset (Atom b)) (c : ℕ → Option (Atom b)) (t : ℕ)
    (hh : (program.body.selection (atomInput b) p
      (tupleCode (List.ofFn (vertexCode b ∘ α)))).FirstStabilization B c t) :
    program.body.output.value (atomInput b) p
      (Fin.cons (stateCode (B t)) (Fin.cons (tupleCode (List.ofFn (vertexCode b ∘ α))) Fin.elim0)) =
        decide (∑ v, b v = 0) := by
  obtain ⟨x,hx,hcons,hoff,hc⟩ := (anchoredParents α).terminal_complete α
    (program.body.selection (atomInput b) p (tupleCode (List.ofFn (vertexCode b ∘ α))))
    (fun x => selection_candidates p hp α hα x hn)
    (fun x _ hoff => selection_transitive p hp α hα x hoff hn) hh
  rw [hx]
  exact value_output p hp α hα x hcons hoff hc hn

lemma body_value (p : Polynomial ℝ) (hp : GridResources p b)
    (α : Fin 4 → Vertex n) (hα : AnchoredTree.Resolving (boxGraph n) α) (hn : 1 ≤ n) :
    program.body.formula.eval (atomInput b) p
      (Fin.cons (tupleCode (List.ofFn (vertexCode b ∘ α))) Fin.elim0) =
        some (decide (∑ v, b v = 0)) := by
  apply program.body.value_constant (atomInput b) p (fun i => vertexBlockSet b (α i))
    (fun i => ?_) hp.basic
  · exact terminal_output p hp α hα hn
  · apply Finset.mem_union_right
    rw [vertexBlocks_grid hn]
    exact Finset.mem_image.mpr ⟨α _,Finset.mem_univ _,rfl⟩

end QuotedGrid

end





noncomputable section

open Classical WitnessedChoice WitnessedChoice.BGS Hereditary

variable {n : ℕ} {b : Vertex n → Scalar}

namespace QuotedGrid

open QuotedTerm QuotedFormula SourceSyntax SourceProgram

attribute [local irreducible] QuotedFormula.resolving

lemma mem_grid_blockParameters {k : ℕ} (env : Fin k → HF (Atom b)) (hn : 1 ≤ n) (z : HF (Atom b)) :
    z ∈ elements ((QuotedTerm.blockParameters : QuotedTerm k).meaning (atomInput b) env) ↔
      ∃ α : Fin 4 → Vertex n, tupleCode (List.ofFn (vertexCode b ∘ α)) = z := by
  rw [blockParameters,mem_tupleProduct,quoted_vertexBlocks hn env,elements_ofFinset]
  constructor
  · rintro ⟨f,hf,hz⟩
    have hh (i : Fin 4) : ∃ v : Vertex n, vertexCode b v = f i := by
      obtain ⟨v,_,hv⟩ := Finset.mem_image.mp (hf i)
      exact ⟨v,hv⟩
    choose α hα using hh
    exact ⟨α,(congrArg (fun f => tupleCode (List.ofFn f)) (funext hα)).trans hz⟩
  · rintro ⟨α,hz⟩
    exact ⟨vertexCode b ∘ α,fun i => Finset.mem_image.mpr ⟨α i,Finset.mem_univ _,rfl⟩,hz⟩

lemma mem_parameters (p : Polynomial ℝ) (hp : GridResources p b) (hn : 1 ≤ n) (z : HF (Atom b)) :
    z ∈ elements (SourceProgram.parameters.value (atomInput b) p Fin.elim0) ↔
      ∃ α : Fin 4 → Vertex n, AnchoredTree.Resolving (boxGraph n) α ∧
        tupleCode (List.ofFn (vertexCode b ∘ α)) = z := by
  let env : Fin 1 → HF (Atom b) := Fin.cons (distancesCode b (boxGraph n)) Fin.elim0
  have hm (α : Fin 4 → Vertex n) :
      (resolving (var 0) QuotedTerm.vertexBlocks (var 1)).meaning (atomInput b)
        (Fin.cons (tupleCode (List.ofFn (vertexCode b ∘ α))) env) ↔
          AnchoredTree.Resolving (boxGraph n) α := by
    exact meaning_resolving (atomInput b) _ (var 0) QuotedTerm.vertexBlocks (var 1)
      (vertexCode b) (vertexCode_injective hn) (boxGraph n) (boxGraph_connected n) α rfl
      (quoted_vertexBlocks hn _) rfl (vertex_card_le_atoms hn)
  rw [SourceProgram.parameters,CPTTerm.value_letIn,value_distances _ p hp hn,CPTTerm.value_quoted]
  simp only [QuotedTerm.meaning_filter,elements_ofFinset,Finset.mem_filter]
  rw [mem_grid_blockParameters env hn z]
  constructor
  · rintro ⟨⟨α,rfl⟩,hr⟩
    exact ⟨α,(hm α).mp hr,rfl⟩
  · rintro ⟨α,hα,rfl⟩
    exact ⟨⟨α,rfl⟩,(hm α).mpr hα⟩

lemma mem_parameterTerm (p : Polynomial ℝ) (hp : GridResources p b) (hn : 1 ≤ n) (z : HF (Atom b)) :
    z ∈ elements (program.parameterTerm.value (atomInput b) p Fin.elim0) ↔
      ∃ α : Fin 4 → Vertex n, AnchoredTree.Resolving (boxGraph n) α ∧
        tupleCode (List.ofFn (vertexCode b ∘ α)) = z := by
  rw [ClosedGuardedProgram.parameterTerm,CPTTerm.value_letIn,CPTTerm.value_quoted]
  simp only [QuotedTerm.meaning_filter,elements_ofFinset,Finset.mem_filter,meaning_mem,meaning_var,
    Fin.cons_zero,Fin.cons_one]
  change (z ∈ elements (QuotedTerm.blockParameters.meaning (atomInput b) _) ∧
    z ∈ elements (SourceProgram.parameters.value (atomInput b) p Fin.elim0)) ↔ _
  rw [mem_parameters p hp hn z]
  constructor
  · exact fun h => h.2
  · rintro ⟨α,hα,hz⟩
    exact ⟨(mem_grid_blockParameters _ hn z).mpr ⟨α,hz⟩,α,hα,hz⟩

lemma parameterTerm_nonempty (p : Polynomial ℝ) (hp : GridResources p b) (hn : 1 ≤ n) :
    (elements (program.parameterTerm.value (atomInput b) p Fin.elim0)).Nonempty := by
  refine ⟨tupleCode (List.ofFn (vertexCode b ∘ cornerAnchors n)),(mem_parameterTerm p hp hn _).mpr
    ⟨cornerAnchors n,?_,rfl⟩⟩
  intro u v h
  exact cornerAnchors_resolve u v (fun i => congrFun h i)

end QuotedGrid

end





noncomputable section

open Classical WitnessedChoice WitnessedChoice.BGS Hereditary

variable {n : ℕ} {b : Vertex n → Scalar}

namespace QuotedGrid

open SourceProgram

attribute [local irreducible] SourceProgram.parameters SourceProgram.candidates
  SourceProgram.cycles SourceProgram.output

lemma formula_value (p : Polynomial ℝ) (hp : GridResources p b) (hn : 1 ≤ n) :
    program.formula.eval (atomInput b) p Fin.elim0 = some (decide (∑ v, b v = 0)) := by
  have he (z : HF (Atom b)) (hz : z ∈ elements (program.parameterTerm.value (atomInput b) p Fin.elim0)) :
      program.body.formula.eval (atomInput b) p (Fin.cons z Fin.elim0) =
        some (decide (∑ v, b v = 0)) := by
    obtain ⟨α,hα,rfl⟩ := (mem_parameterTerm p hp hn z).mp hz
    exact body_value p hp α hα hn
  rw [ClosedGuardedProgram.formula,
    Formula.eval_existsIn_on _ p _ _ _ (program.parameterTerm.eval_value _ p _) he]
  apply congrArg some
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  constructor
  · exact fun ⟨_,_,h⟩ => h
  · intro h
    obtain ⟨z,hz⟩ := parameterTerm_nonempty p hp hn
    exact ⟨z,hz,h⟩

end QuotedGrid

end

end WitnessedSeparation.Grid

end OAI
