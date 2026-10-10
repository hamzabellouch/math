import OAI.Computability.WitnessedChoice.GridGeometry

namespace OAI


namespace WitnessedChoice

noncomputable section

open Classical

namespace AnchoredTree

variable {V : Type} [Fintype V]

def key (G : SimpleGraph V) (α : Fin 4 → V) (v : V) : Lex (Fin 4 → ℕ) :=
  toLex (fun i => G.dist (α i) v)

def Resolving (G : SimpleGraph V) (α : Fin 4 → V) : Prop := Function.Injective (key G α)

def Eligible (G : SimpleGraph V) (r v w : V) : Prop := G.Adj v w ∧ G.dist r w + 1 = G.dist r v

omit [Fintype V] in
lemma root_lt (G : SimpleGraph V) (hG : G.Connected) (α : Fin 4 → V)
    (v : V) (hv : v ≠ α 0) : key G α (α 0) < key G α v := by
  refine ⟨0,?_,?_⟩
  · intro j hj; exact (Fin.not_lt_zero j hj).elim
  · change G.dist (α 0) (α 0) < G.dist (α 0) v
    rw [G.dist_self]
    exact Nat.pos_of_ne_zero (fun h => hv ((hG (α 0) v).dist_eq_zero_iff.mp h).symm)

omit [Fintype V] in
lemma least_iff_root (G : SimpleGraph V) (hG : G.Connected) (α : Fin 4 → V) (v : V) :
    (∀ w, ¬key G α w < key G α v) ↔ v = α 0 := by
  constructor
  · intro h; by_contra hn; exact h _ (root_lt G hG α v hn)
  · rintro rfl w hw
    by_cases h : w = α 0
    · subst w; exact lt_irrefl _ hw
    · exact (lt_asymm hw (root_lt G hG α w h))

omit [Fintype V] in
lemma exists_eligible (G : SimpleGraph V) (hG : G.Connected) (r v : V) (hv : v ≠ r) :
    ∃ w, Eligible G r v w := by
  obtain ⟨p,hp⟩ := hG.exists_walk_length_eq_dist v r
  cases p with
  | nil => exact (hv rfl).elim
  | @cons _ w _ hadj q =>
    refine ⟨w,hadj,?_⟩
    have hle := G.dist_le q
    have hd := hadj.diff_dist_adj (u := r)
    simp only [SimpleGraph.Walk.length_cons] at hp
    rw [G.dist_comm (u := v) (v := r)] at hp
    rw [G.dist_comm (u := w) (v := r)] at hle
    omega

omit [Fintype V] in
lemma exists_min_key (G : SimpleGraph V) (α : Fin 4 → V) (D : Finset V) (hD : D.Nonempty) :
    ∃ v ∈ D, ∀ w ∈ D, ¬key G α w < key G α v := by
  let K := D.image (key G α)
  have hK : K.Nonempty := hD.image _
  obtain ⟨v,hv,he⟩ := Finset.mem_image.mp (Finset.min'_mem K hK)
  refine ⟨v,hv,?_⟩
  intro w hw hlt
  have hm := Finset.min'_le K (key G α w) (Finset.mem_image.mpr ⟨w,hw,rfl⟩)
  rw [←he] at hm
  exact (not_lt_of_ge hm) hlt

lemma exists_parent (G : SimpleGraph V) (hG : G.Connected) (α : Fin 4 → V)
    (v : V) (hv : v ≠ α 0) :
    ∃ w, Eligible G (α 0) v w ∧ ∀ z, Eligible G (α 0) v z → ¬key G α z < key G α w := by
  obtain ⟨w,hw⟩ := exists_eligible G hG (α 0) v hv
  obtain ⟨z,hz,hm⟩ := exists_min_key G α (Finset.univ.filter (Eligible G (α 0) v))
    ⟨w,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hw⟩⟩
  exact ⟨z,(Finset.mem_filter.mp hz).2,fun y hy => hm y (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hy⟩)⟩

def parent (G : SimpleGraph V) (hG : G.Connected) (α : Fin 4 → V) (v : V) : V :=
  if hv : v = α 0 then α 0 else (exists_parent G hG α v hv).choose

lemma parent_property (G : SimpleGraph V) (hG : G.Connected) (α : Fin 4 → V)
    (v : V) (hv : v ≠ α 0) :
    Eligible G (α 0) v (parent G hG α v) ∧
      ∀ z, Eligible G (α 0) v z → ¬key G α z < key G α (parent G hG α v) := by
  rw [parent,dite_eq_right hv]
  exact (exists_parent G hG α v hv).choose_spec

def rooted (G : SimpleGraph V) (hG : G.Connected) (α : Fin 4 → V) : TreeTest.RootedTree V where
  root := α 0
  parent := parent G hG α
  level := G.dist (α 0)
  parent_lower v hv := by have h := (parent_property G hG α v hv).1.2; omega

lemma parent_iff (G : SimpleGraph V) (hG : G.Connected) (α : Fin 4 → V)
    (hα : Resolving G α) (v w : V) :
    (Eligible G (α 0) v w ∧ ∀ z, Eligible G (α 0) v z → ¬key G α z < key G α w) ↔
      v ≠ α 0 ∧ (rooted G hG α).parent v = w := by
  constructor
  · rintro ⟨hw,hm⟩
    have hv : v ≠ α 0 := by intro hh; have hd := hw.2; rw [hh,G.dist_self] at hd; omega
    refine ⟨hv,?_⟩
    have hp := parent_property G hG α v hv
    apply hα
    exact le_antisymm (le_of_not_gt (hp.2 w hw)) (le_of_not_gt (hm _ hp.1))
  · rintro ⟨hv,rfl⟩
    exact parent_property G hG α v hv

end AnchoredTree

end

end WitnessedChoice



namespace WitnessedChoice.BGS

noncomputable section

open Classical WitnessedSeparation WitnessedSeparation.Hereditary QuotedTerm

namespace QuotedFormula

variable {A V : Type} [Fintype A] [Fintype V] {k : ℕ}

lemma meaning_vertexLt (S : Input A) (env : Fin k → HF A)
    (ats R ut vt : QuotedTerm k) (code : V → HF A) (hc : Function.Injective code)
    (G : SimpleGraph V) (hG : G.Connected) (α : Fin 4 → V) (u v : V)
    (hα : ats.meaning S env = tupleCode (List.ofFn (code ∘ α)))
    (hR : R.meaning S env = ofFinset ((BFS.closure G (Fintype.card A)).image (distanceCode code)))
    (hu : ut.meaning S env = code u) (hv : vt.meaning S env = code v)
    (hcard : Fintype.card V ≤ Fintype.card A) :
    (vertexLt ats R ut vt).meaning S env ↔ AnchoredTree.key G α u < AnchoredTree.key G α v := by
  have hdU (i : Fin 4) : (distanceAt R (ats.component i.val) ut).meaning S env = ordinal (G.dist (α i) u) :=
    meaning_distanceAt S env R _ _ code hc G hG _ _ hR
      (meaning_component_ofFn S env ats (code ∘ α) hα i) hu hcard
  have hdV (i : Fin 4) : (distanceAt R (ats.component i.val) vt).meaning S env = ordinal (G.dist (α i) v) :=
    meaning_distanceAt S env R _ _ code hc G hG _ _ hR
      (meaning_component_ofFn S env ats (code ∘ α) hα i) hv hcard
  simp only [vertexLt,meaning_anyFin,meaning_and,meaning_allFin,meaning_mem,hdU,hdV,
    ordinal_mem_elements]
  change (∃ i : Fin 4, (∀ j : Fin 4, _) ∧ _) ↔ _
  have hm (i j : Fin 4) :
      (if j.val < i.val then eq (distanceAt R (ats.component j.val) ut)
        (distanceAt R (ats.component j.val) vt) else truth).meaning S env ↔
      (j < i → G.dist (α j) u = G.dist (α j) v) := by
    split_ifs with h
    · simp only [meaning_eq,hdU,hdV,ordinal_injective.eq_iff]
      simp only [Fin.lt_def,h,true_implies]
    · simp [truth, Fin.lt_def, h]
  simp only [hm]
  rfl

lemma meaning_resolving (S : Input A) (env : Fin k → HF A)
    (ats VT R : QuotedTerm k) (code : V → HF A) (hc : Function.Injective code)
    (G : SimpleGraph V) (hG : G.Connected) (α : Fin 4 → V)
    (hα : ats.meaning S env = tupleCode (List.ofFn (code ∘ α)))
    (hV : VT.meaning S env = ofFinset (Finset.univ.image code))
    (hR : R.meaning S env = ofFinset ((BFS.closure G (Fintype.card A)).image (distanceCode code)))
    (hcard : Fintype.card V ≤ Fintype.card A) :
    (resolving ats VT R).meaning S env ↔ AnchoredTree.Resolving G α := by
  simp only [resolving,meaning_allIn,meaning_imp,meaning_allFin,meaning_eq,meaning_var,
    QuotedTerm.meaning_up,hV,elements_ofFinset,Finset.mem_image,Finset.mem_univ,true_and,
    forall_exists_index,forall_apply_eq_imp_iff,Fin.cons_zero,Fin.cons_one]
  have hd (u v : V) (i : Fin 4) (w : V) (wt : QuotedTerm (k+2))
      (hw : wt.meaning S (Fin.cons (code v) (Fin.cons (code u) env)) = code w) :
      (distanceAt R.up.up (ats.up.up.component i.val) wt).meaning S
        (Fin.cons (code v) (Fin.cons (code u) env)) = ordinal (G.dist (α i) w) := by
    apply meaning_distanceAt S _ _ _ _ code hc G hG _ _ _ _ hw hcard
    · simpa only [QuotedTerm.meaning_up] using hR
    · apply meaning_component_ofFn S _ _ (code ∘ α) _ i
      simpa only [QuotedTerm.meaning_up] using hα
  have hd₁ (u v : V) (i : Fin 4) := hd u v i u (var 1) (by simp)
  have hd₀ (u v : V) (i : Fin 4) := hd u v i v (var 0) (by simp)
  simp only [hd₁,hd₀,ordinal_injective.eq_iff,hc.eq_iff]
  constructor
  · intro h u v huv
    exact h u v (fun i => congrFun huv i)
  · intro h u v huv
    apply h
    exact funext huv

end QuotedFormula

end

end WitnessedChoice.BGS



namespace WitnessedSeparation.Grid

noncomputable section

open Classical WitnessedChoice WitnessedChoice.BGS Hereditary

variable {n : ℕ} {b : Vertex n → Scalar}

lemma configuration_exists (hn : 1 ≤ n) (v : Vertex n) : Nonempty (Configuration b v) := by
  obtain ⟨e0,_⟩ := incident_on_axis hn v 0
  exact ⟨{ state := fun e => ⟨0,extendVertexScalars b v e0 0 e⟩
           compatible := by intro e e' f hf hf'; rfl
           charge := extendVertexScalars_charge e0 0 }⟩

@[simp] lemma mem_edgeBlockSet (e : Edge n) (a : Atom b) :
    a ∈ edgeBlockSet b e ↔ ∃ s : LocalGroup e, a = .inl ⟨e,s⟩ := by
  simp only [edgeBlockSet,Finset.mem_image,Finset.mem_univ,true_and]
  aesop

@[simp] lemma mem_vertexBlockSet (v : Vertex n) (a : Atom b) :
    a ∈ vertexBlockSet b v ↔ ∃ s : Configuration b v, a = .inr ⟨v,s⟩ := by
  simp only [vertexBlockSet,Finset.mem_image,Finset.mem_univ,true_and]
  aesop

lemma edgeBlockSet_injective : Function.Injective (edgeBlockSet b) := by
  intro e f h
  have hm : (Sum.inl ⟨e,1⟩ : Atom b) ∈ edgeBlockSet b e := by simp
  rw [h,mem_edgeBlockSet] at hm
  obtain ⟨t,ht⟩ := hm
  exact congrArg Sigma.fst (Sum.inl.inj ht)

lemma vertexBlockSet_injective (hn : 1 ≤ n) : Function.Injective (vertexBlockSet b) := by
  intro v w h
  obtain ⟨s⟩ := configuration_exists (b := b) hn v
  have hm : (Sum.inr ⟨v,s⟩ : Atom b) ∈ vertexBlockSet b v := by simp
  rw [h,mem_vertexBlockSet] at hm
  obtain ⟨t,ht⟩ := hm
  exact congrArg Sigma.fst (Sum.inr.inj ht)

lemma edgeRow_grid (e : Edge n) (s : LocalGroup e) :
    WitnessedChoice.edgeRow (atomInput b) (.inl ⟨e,s⟩) = edgeBlockSet b e := by
  ext a
  simp only [WitnessedChoice.edgeRow,WitnessedChoice.edgeAtoms,Finset.mem_filter,
    Finset.mem_univ,true_and,atomInput,decide_eq_true_eq,mem_edgeBlockSet]
  constructor
  · rintro ⟨_,h⟩
    cases h with | eb e s t => exact ⟨t,rfl⟩
  · rintro ⟨t,rfl⟩
    exact ⟨.ed e t,.eb e s t⟩

lemma vertexRow_grid (v : Vertex n) (s : Configuration b v) :
    WitnessedChoice.vertexRow (atomInput b) (.inr ⟨v,s⟩) = vertexBlockSet b v := by
  ext a
  simp only [WitnessedChoice.vertexRow,WitnessedChoice.configAtoms,Finset.mem_filter,
    Finset.mem_univ,true_and,atomInput,decide_eq_true_eq,mem_vertexBlockSet]
  constructor
  · rintro ⟨_,h⟩
    cases h with | vb v s t => exact ⟨t,rfl⟩
  · rintro ⟨t,rfl⟩
    exact ⟨.cf v t,.vb v s t⟩

lemma edgeBlocks_grid : WitnessedChoice.edgeBlocks (atomInput b) =
    Finset.univ.image (edgeBlockSet b) := by
  ext d
  simp only [WitnessedChoice.edgeBlocks,Finset.mem_image,WitnessedChoice.edgeAtoms,
    Finset.mem_filter,Finset.mem_univ,true_and,atomInput,decide_eq_true_eq]
  constructor
  · rintro ⟨a,h,rfl⟩
    cases h with | ed e s => exact ⟨e,(edgeRow_grid e s).symm⟩
  · rintro ⟨e,rfl⟩
    exact ⟨.inl ⟨e,1⟩,.ed e 1,edgeRow_grid e 1⟩

lemma vertexBlocks_grid (hn : 1 ≤ n) : WitnessedChoice.vertexBlocks (atomInput b) =
    Finset.univ.image (vertexBlockSet b) := by
  ext d
  simp only [WitnessedChoice.vertexBlocks,Finset.mem_image,WitnessedChoice.configAtoms,
    Finset.mem_filter,Finset.mem_univ,true_and,atomInput,decide_eq_true_eq]
  constructor
  · rintro ⟨a,h,rfl⟩
    cases h with | cf v s => exact ⟨v,(vertexRow_grid v s).symm⟩
  · rintro ⟨v,rfl⟩
    obtain ⟨s⟩ := configuration_exists (b := b) hn v
    exact ⟨.inr ⟨v,s⟩,.cf v s,vertexRow_grid v s⟩

def vertexCode (b : Vertex n → Scalar) (v : Vertex n) : HF (Atom b) := stateCode (vertexBlockSet b v)

def edgeCode (b : Vertex n → Scalar) (e : Edge n) : HF (Atom b) := stateCode (edgeBlockSet b e)

lemma vertexCode_injective (hn : 1 ≤ n) : Function.Injective (vertexCode b) :=
  fun _ _ h => vertexBlockSet_injective hn (stateCode_inj.mp h)

lemma edgeCode_injective : Function.Injective (edgeCode b) :=
  fun _ _ h => edgeBlockSet_injective (stateCode_inj.mp h)

lemma blockIncident_grid (hn : 1 ≤ n) (v : Vertex n) (e : Edge n) :
    blockIncident (atomInput b) (vertexCode b v) (edgeCode b e) ↔ incident v e := by
  simp only [blockIncident,vertexCode,edgeCode,exists_stateCode,mem_vertexBlockSet,
    mem_edgeBlockSet]
  constructor
  · rintro ⟨_,⟨s,rfl⟩,_,⟨t,rfl⟩,h⟩
    rw [inputHF_atoms] at h
    change decide (AtomRelation b .I (.inr ⟨v,s⟩) (.inl ⟨e,t⟩)) = true at h
    have h := of_decide_eq_true h
    cases h with | inc v s e => exact e.property
  · intro h
    obtain ⟨s⟩ := configuration_exists (b := b) hn v
    exact ⟨.inr ⟨v,s⟩,⟨s,rfl⟩,.inl ⟨e,s.state ⟨e,h⟩⟩,⟨_,rfl⟩,
      by rw [inputHF_atoms]; exact decide_eq_true (.inc v s ⟨e,h⟩)⟩

end





noncomputable section

open Classical WitnessedChoice WitnessedChoice.BGS Hereditary

variable {n : ℕ} {b : Vertex n → Scalar}

def edgeGraph (T : Finset (Edge n)) : SimpleGraph (Vertex n) where
  Adj u v := ∃ e ∈ T, (u = tail e ∧ v = head e) ∨ (v = tail e ∧ u = head e)
  symm := ⟨by intro u v; rintro ⟨e,he,h⟩; exact ⟨e,he,h.symm⟩⟩
  loopless := ⟨by
    intro v
    rintro ⟨e,he,h|h⟩
    all_goals exact head_ne_tail e (h.2.symm.trans h.1)⟩

lemma edgeGraph_univ : edgeGraph (Finset.univ : Finset (Edge n)) = boxGraph n := by
  ext u v
  simp only [edgeGraph,Finset.mem_univ,true_and,boxGraph_adj_iff]

lemma blockAdjacent_edges (hn : 1 ≤ n) (T : Finset (Edge n)) (u v : Vertex n) :
    blockAdjacent (atomInput b) (ofFinset (T.image (edgeCode b))) (vertexCode b u) (vertexCode b v) ↔
      (edgeGraph T).Adj u v := by
  simp only [blockAdjacent,(vertexCode_injective hn).ne_iff,elements_ofFinset,
    Finset.mem_image,exists_exists_and_eq_and,blockIncident_grid hn,edgeGraph]
  constructor
  · rintro ⟨hne,e,he,hu,hv⟩
    refine ⟨e,he,?_⟩
    rcases hu with hu | hu <;> rcases hv with hv | hv
    · exact (hne (hu.symm.trans hv)).elim
    · exact Or.inr ⟨hv.symm,hu.symm⟩
    · exact Or.inl ⟨hu.symm,hv.symm⟩
    · exact (hne (hu.symm.trans hv)).elim
  · rintro ⟨e,he,(⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)⟩
    · exact ⟨(head_ne_tail e).symm,e,he,Or.inr rfl,Or.inl rfl⟩
    · exact ⟨head_ne_tail e,e,he,Or.inl rfl,Or.inr rfl⟩

lemma vertex_card_le_atoms (hn : 1 ≤ n) : Fintype.card (Vertex n) ≤ Fintype.card (Atom b) := by
  let f (v : Vertex n) : Atom b := .inr ⟨v,(configuration_exists (b := b) hn v).some⟩
  apply Fintype.card_le_of_injective f
  intro v w h
  exact congrArg Sigma.fst (Sum.inr.inj h)

lemma quoted_vertexBlocks {k : ℕ} (hn : 1 ≤ n) (env : Fin k → HF (Atom b)) :
    (QuotedTerm.vertexBlocks : QuotedTerm k).meaning (atomInput b) env =
      ofFinset (Finset.univ.image (vertexCode b)) := by
  rw [QuotedTerm.meaning_vertexBlocks,vertexBlocks_grid hn,Finset.image_image]
  rfl

lemma quoted_edgeBlocks {k : ℕ} (env : Fin k → HF (Atom b)) :
    (QuotedTerm.edgeBlocks : QuotedTerm k).meaning (atomInput b) env =
      ofFinset (Finset.univ.image (edgeCode b)) := by
  rw [QuotedTerm.meaning_edgeBlocks,edgeBlocks_grid,Finset.image_image]
  rfl

end





noncomputable section

open Classical

variable {n : ℕ}

lemma xy_incident_face (i : Fin n) (j k : Fin (n+1)) (i' k' : Fin (n+1)) (j' : Fin n) (v : Vertex n)
    (hv : incident v (ex i j k)) (hw : incident v (ey i' j' k')) :
    ∃ f : Face n, cycle f (ex i j k) ≠ 0 ∧ cycle f (ey i' j' k') ≠ 0 := by
  rcases hv with hv|hv
  all_goals subst v
  all_goals rcases hw with hw|hw
  all_goals simp only [head,tail] at hw
  all_goals rcases hw with ⟨hi,hj,hk⟩
  all_goals refine ⟨.inl (i,j',k),?_,?_⟩
  all_goals solve
    | (convert cycle_faceSide (n := n) (.inl (i,j',k)) 0 using 1 ; simp_all [faceSide])
    | (convert cycle_faceSide (n := n) (.inl (i,j',k)) 1 using 1 ; simp_all [faceSide])
    | (convert cycle_faceSide (n := n) (.inl (i,j',k)) 2 using 1 ; simp_all [faceSide])
    | (convert cycle_faceSide (n := n) (.inl (i,j',k)) 3 using 1 ; simp_all [faceSide])

lemma xz_incident_face (i : Fin n) (j k : Fin (n+1)) (i' j' : Fin (n+1)) (k' : Fin n) (v : Vertex n)
    (hv : incident v (ex i j k)) (hw : incident v (ez i' j' k')) :
    ∃ f : Face n, cycle f (ex i j k) ≠ 0 ∧ cycle f (ez i' j' k') ≠ 0 := by
  rcases hv with hv|hv
  all_goals subst v
  all_goals rcases hw with hw|hw
  all_goals simp only [head,tail] at hw
  all_goals rcases hw with ⟨hi,hj,hk⟩
  all_goals refine ⟨.inr (.inl (i,j,k')),?_,?_⟩
  all_goals solve
    | (convert cycle_faceSide (n := n) (.inr (.inl (i,j,k'))) 0 using 1 ; simp_all [faceSide])
    | (convert cycle_faceSide (n := n) (.inr (.inl (i,j,k'))) 1 using 1 ; simp_all [faceSide])
    | (convert cycle_faceSide (n := n) (.inr (.inl (i,j,k'))) 2 using 1 ; simp_all [faceSide])
    | (convert cycle_faceSide (n := n) (.inr (.inl (i,j,k'))) 3 using 1 ; simp_all [faceSide])

lemma yz_incident_face (j : Fin n) (i k : Fin (n+1)) (i' j' : Fin (n+1)) (k' : Fin n) (v : Vertex n)
    (hv : incident v (ey i j k)) (hw : incident v (ez i' j' k')) :
    ∃ f : Face n, cycle f (ey i j k) ≠ 0 ∧ cycle f (ez i' j' k') ≠ 0 := by
  rcases hv with hv|hv
  all_goals subst v
  all_goals rcases hw with hw|hw
  all_goals simp only [head,tail] at hw
  all_goals rcases hw with ⟨hi,hj,hk⟩
  all_goals refine ⟨.inr (.inr (i,j,k')),?_,?_⟩
  all_goals solve
    | (convert cycle_faceSide (n := n) (.inr (.inr (i,j,k'))) 0 using 1 ; simp_all [faceSide])
    | (convert cycle_faceSide (n := n) (.inr (.inr (i,j,k'))) 1 using 1 ; simp_all [faceSide])
    | (convert cycle_faceSide (n := n) (.inr (.inr (i,j,k'))) 2 using 1 ; simp_all [faceSide])
    | (convert cycle_faceSide (n := n) (.inr (.inr (i,j,k'))) 3 using 1 ; simp_all [faceSide])

lemma incident_perpendicular_face (v : Vertex n) (e e' : Edge n)
    (hv : incident v e) (hw : incident v e') (ha : edgeAxis e ≠ edgeAxis e') :
    ∃ f : Face n, cycle f e ≠ 0 ∧ cycle f e' ≠ 0 := by
  have swap : (∃ f : Face n, cycle f e' ≠ 0 ∧ cycle f e ≠ 0) →
      ∃ f : Face n, cycle f e ≠ 0 ∧ cycle f e' ≠ 0 := by
    rintro ⟨f,hf,hf'⟩; exact ⟨f,hf',hf⟩
  rcases e with ⟨i,j,k⟩ | (⟨i,j,k⟩ | ⟨i,j,k⟩)
  all_goals rcases e' with ⟨i',j',k'⟩ | (⟨i',j',k'⟩ | ⟨i',j',k'⟩)
  all_goals first
    | exact (ha rfl).elim
    | exact xy_incident_face _ _ _ _ _ _ v hv hw
    | exact xz_incident_face _ _ _ _ _ _ v hv hw
    | exact yz_incident_face _ _ _ _ _ _ v hv hw
    | exact swap (xy_incident_face _ _ _ _ _ _ v hw hv)
    | exact swap (xz_incident_face _ _ _ _ _ _ v hw hv)
    | exact swap (yz_incident_face _ _ _ _ _ _ v hw hv)

end





noncomputable section

open Classical SimpleGraph

variable {n : ℕ}

lemma square_common_neighbors (f : Face n) (i : Fin 4) (v : Vertex n)
    (h₀ : (boxGraph n).Adj (faceCorner f i) v)
    (h₂ : (boxGraph n).Adj (faceCorner f (i+2)) v) :
    v = faceCorner f (i+1) ∨ v = faceCorner f (i+3) := by
  rcases f with ⟨x,y,z⟩ | (⟨x,y,z⟩ | ⟨x,y,z⟩) <;> fin_cases i
  all_goals
    simp [boxGraph,boxProd_adj,pathGraph_adj,faceCorner,Prod.ext_iff,Fin.ext_iff] at h₀ h₂ ⊢
    omega

end





noncomputable section

open Classical

abbrev Direction := Fin 3 × Bool

def directionVector (d : Direction) : Fin 3 → ℤ :=
  fun a => if a = d.1 then (if d.2 then 1 else -1) else 0

def oppositeDirection (d : Direction) : Direction := (d.1,!d.2)

lemma direction_neg (d : Direction) : directionVector (oppositeDirection d) = -directionVector d := by
  rcases d with ⟨a,b⟩
  funext i
  cases b <;> by_cases h : i = a <;> simp [directionVector,oppositeDirection,h]

lemma four_direction_pattern : ∀ d₀ d₁ d₂ d₃ : Direction,
    directionVector d₀ + directionVector d₁ + directionVector d₂ + directionVector d₃ = 0 →
    directionVector d₀ + directionVector d₁ ≠ 0 →
    directionVector d₁ + directionVector d₂ ≠ 0 →
    d₂ = oppositeDirection d₀ ∧ d₃ = oppositeDirection d₁ ∧ d₀.1 ≠ d₁.1 := by
  decide

end





noncomputable section

open Classical SimpleGraph

variable {n : ℕ}

def vertexInt (v : Vertex n) : Fin 3 → ℤ := fun a => (vertexCoord v a).val

lemma vertexInt_injective : Function.Injective (vertexInt (n := n)) := by
  intro v w h
  apply vertexCoord_injective
  funext a
  apply Fin.ext
  exact Int.ofNat_inj.mp (congrFun h a)

lemma head_vertexInt (e : Edge n) :
    vertexInt (head e) = vertexInt (tail e) + directionVector (edgeAxis e,true) := by
  rcases e with ⟨x,y,z⟩ | (⟨x,y,z⟩ | ⟨x,y,z⟩)
  all_goals
    funext a
    fin_cases a <;> simp [vertexInt,vertexCoord,head,tail,directionVector,edgeAxis]

lemma endpoints_direction (u v : Vertex n) (e : Edge n)
    (h : (u = tail e ∧ v = head e) ∨ (v = tail e ∧ u = head e)) :
    ∃ d : Direction, d.1 = edgeAxis e ∧ vertexInt v - vertexInt u = directionVector d := by
  rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact ⟨(edgeAxis e,true),rfl,by rw [head_vertexInt]; abel⟩
  · refine ⟨(edgeAxis e,false),rfl,?_⟩
    have ht : directionVector (edgeAxis e,false) = -directionVector (edgeAxis e,true) :=
      direction_neg (edgeAxis e,true)
    rw [head_vertexInt,ht]
    abel

lemma square_consecutive_perpendicular (v : Fin 4 → Vertex n) (e : Fin 4 → Edge n)
    (hv : Function.Injective v)
    (he : ∀ i, (v i = tail (e i) ∧ v (i+1) = head (e i)) ∨
      (v (i+1) = tail (e i) ∧ v i = head (e i))) :
    edgeAxis (e 0) ≠ edgeAxis (e 1) := by
  choose d hd hvec using fun i => endpoints_direction (v i) (v (i+1)) (e i) (he i)
  have hzero : directionVector (d 0) + directionVector (d 1) +
      directionVector (d 2) + directionVector (d 3) = 0 := by
    rw [← hvec 0,← hvec 1,← hvec 2,← hvec 3]
    change (vertexInt (v 1) - vertexInt (v 0)) + (vertexInt (v 2) - vertexInt (v 1)) +
      (vertexInt (v 3) - vertexInt (v 2)) + (vertexInt (v 0) - vertexInt (v 3)) = 0
    abel
  have hz₁ : directionVector (d 0) + directionVector (d 1) ≠ 0 := by
    intro h
    have hh : vertexInt (v 2) = vertexInt (v 0) := by
      have h' : vertexInt (v 2) - vertexInt (v 0) = 0 := by
        calc
          _ = directionVector (d 0) + directionVector (d 1) := by
            rw [← hvec 0,← hvec 1]
            change vertexInt (v 2) - vertexInt (v 0) =
              (vertexInt (v 1) - vertexInt (v 0)) + (vertexInt (v 2) - vertexInt (v 1))
            abel
          _ = 0 := h
      exact sub_eq_zero.mp h'
    exact (by decide : (2 : Fin 4) ≠ 0) (hv (vertexInt_injective hh))
  have hz₂ : directionVector (d 1) + directionVector (d 2) ≠ 0 := by
    intro h
    have hh : vertexInt (v 3) = vertexInt (v 1) := by
      have h' : vertexInt (v 3) - vertexInt (v 1) = 0 := by
        calc
          _ = directionVector (d 1) + directionVector (d 2) := by
            rw [← hvec 1,← hvec 2]
            change vertexInt (v 3) - vertexInt (v 1) =
              (vertexInt (v 2) - vertexInt (v 1)) + (vertexInt (v 3) - vertexInt (v 2))
            abel
          _ = 0 := h
      exact sub_eq_zero.mp h'
    exact (by decide : (3 : Fin 4) ≠ 1) (hv (vertexInt_injective hh))
  simpa only [hd] using (four_direction_pattern _ _ _ _ hzero hz₁ hz₂).2.2

lemma faceCorner_index_injective (f : Face n) : Function.Injective (faceCorner f) := by
  intro i j
  rcases f with ⟨x,y,z⟩ | (⟨x,y,z⟩ | ⟨x,y,z⟩) <;> fin_cases i <;> fin_cases j
  all_goals simp [faceCorner,castSucc_ne_succ_self,succ_ne_castSucc_self]

lemma incident_faceSide (f : Face n) (i : Fin 4) (v : Vertex n) :
    incident v (faceSide f i) ↔ v = faceCorner f i ∨ v = faceCorner f (i+1) := by
  rcases f with ⟨x,y,z⟩ | (⟨x,y,z⟩ | ⟨x,y,z⟩) <;> fin_cases i
  all_goals simp [incident,faceSide,faceCorner,tail,head,ex,ey,ez,or_comm,eq_comm]

lemma square_index_calculation : ∀ i j a b c : Fin 4, i ≠ j →
    (a=i ∨ a=i+1) → (b=i ∨ b=i+1) → (b=j ∨ b=j+1) → (c=j ∨ c=j+1) →
    a ≠ b → b ≠ c → c = a+2 := by decide

lemma face_chain_opposite (f : Face n) (i j : Fin 4) (v₀ v₁ v₂ : Vertex n)
    (hij : i ≠ j) (h01 : v₀ ≠ v₁) (h12 : v₁ ≠ v₂)
    (hi₀ : incident v₀ (faceSide f i)) (hi₁ : incident v₁ (faceSide f i))
    (hj₁ : incident v₁ (faceSide f j)) (hj₂ : incident v₂ (faceSide f j)) :
    ∃ k : Fin 4, v₀ = faceCorner f k ∧ v₂ = faceCorner f (k+2) := by
  have h0 : ∃ a, v₀ = faceCorner f a := by
    rcases (incident_faceSide f i v₀).mp hi₀ with h|h <;> exact ⟨_,h⟩
  have h1 : ∃ a, v₁ = faceCorner f a := by
    rcases (incident_faceSide f i v₁).mp hi₁ with h|h <;> exact ⟨_,h⟩
  have h2 : ∃ a, v₂ = faceCorner f a := by
    rcases (incident_faceSide f j v₂).mp hj₂ with h|h <;> exact ⟨_,h⟩
  obtain ⟨a,rfl⟩ := h0
  obtain ⟨b,rfl⟩ := h1
  obtain ⟨c,rfl⟩ := h2
  have hc : c = a+2 := square_index_calculation i j a b c hij
    (by simpa only [incident_faceSide,(faceCorner_index_injective f).eq_iff] using hi₀)
    (by simpa only [incident_faceSide,(faceCorner_index_injective f).eq_iff] using hi₁)
    (by simpa only [incident_faceSide,(faceCorner_index_injective f).eq_iff] using hj₁)
    (by simpa only [incident_faceSide,(faceCorner_index_injective f).eq_iff] using hj₂)
    (fun h => h01 (congrArg _ h)) (fun h => h12 (congrArg _ h))
  exact ⟨a,rfl,congrArg _ hc⟩

lemma edge_eq_of_endpoints (e f : Edge n)
    (h : (tail e=tail f ∧ head e=head f) ∨ (tail e=head f ∧ head e=tail f)) : e=f := by
  rcases e with ⟨x,y,z⟩ | (⟨x,y,z⟩ | ⟨x,y,z⟩)
  all_goals rcases f with ⟨x',y',z'⟩ | (⟨x',y',z'⟩ | ⟨x',y',z'⟩)
  all_goals simp [tail,head,Prod.ext_iff,Fin.ext_iff] at h ⊢
  all_goals omega

end





noncomputable section

open Classical WitnessedChoice WitnessedChoice.TreeTest

variable {n : ℕ}

def symEdge (e : Edge n) : Sym2 (Vertex n) := s(tail e, head e)

lemma symEdge_injective : Function.Injective (symEdge (n := n)) := by
  intro e f h
  apply edge_eq_of_endpoints e f
  exact Sym2.eq_iff.mp h

lemma edgeGraph_edgeFinset (T : Finset (Edge n)) :
    (edgeGraph T).edgeFinset = T.image symEdge := by
  apply Finset.ext
  intro q
  induction q using Sym2.inductionOn with
  | _ u v =>
    rw [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet]
    change (∃ e ∈ T, u = tail e ∧ v = head e ∨ v = tail e ∧ u = head e) ↔ _
    simp only [Finset.mem_image,symEdge,Sym2.eq_iff]
    constructor
    · rintro ⟨e,he, (⟨hu,hv⟩ | ⟨hv,hu⟩)⟩
      · exact ⟨e,he,Or.inl ⟨hu.symm,hv.symm⟩⟩
      · exact ⟨e,he,Or.inr ⟨hv.symm,hu.symm⟩⟩
    · rintro ⟨e,he, (⟨hu,hv⟩ | ⟨hv,hu⟩)⟩
      · exact ⟨e,he,Or.inl ⟨hu.symm,hv.symm⟩⟩
      · exact ⟨e,he,Or.inr ⟨hv.symm,hu.symm⟩⟩

lemma edgeGraph_card (T : Finset (Edge n)) :
    Nat.card (edgeGraph T).edgeSet = T.card := by
  rw [Nat.card_eq_fintype_card,←SimpleGraph.edgeFinset_card,edgeGraph_edgeFinset,
    Finset.card_image_of_injective _ symEdge_injective]

namespace ParentEdges

variable {T : RootedTree (Vertex n)} (P : ParentEdges T)

lemma edge_injective : Function.Injective (fun v : {v : Vertex n // v ≠ T.root} => P.edge v.val v.property) := by
  intro v w h
  apply Subtype.ext
  have hv := P.endpoints v.val v.property
  have hw := P.endpoints w.val w.property
  change P.edge v.val v.property = P.edge w.val w.property at h
  rw [h] at hv
  rcases hv with ⟨hv₁,hv₂⟩ | ⟨hv₁,hv₂⟩ <;>
    rcases hw with ⟨hw₁,hw₂⟩ | ⟨hw₁,hw₂⟩
  · exact hv₁.symm.trans hw₁
  · have he₁ := hv₁.symm.trans hw₂
    have he₂ := hw₁.symm.trans hv₂
    have hlv := T.parent_lower v.val v.property
    have hlw := T.parent_lower w.val w.property
    rw [←he₁] at hlw
    rw [←he₂] at hlv
    omega
  · have he₁ := hv₁.symm.trans hw₂
    have he₂ := hw₁.symm.trans hv₂
    have hlv := T.parent_lower v.val v.property
    have hlw := T.parent_lower w.val w.property
    rw [←he₁] at hlw
    rw [←he₂] at hlv
    omega
  · exact hv₁.symm.trans hw₁

lemma graph_adj (u v : Vertex n) : (edgeGraph P.treeEdges).Adj u v ↔ T.Adj u v := by
  simp only [edgeGraph,treeEdges,Finset.mem_image,Finset.mem_univ,true_and,exists_exists_eq_and]
  constructor
  · rintro ⟨w,h⟩
    rcases P.endpoints w.val w.property with ⟨hh,ht⟩ | ⟨ht,hh⟩
    · rw [hh,ht] at h
      rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact Or.inr ⟨w.property,rfl⟩
      · exact Or.inl ⟨w.property,rfl⟩
    · rw [hh,ht] at h
      rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact Or.inl ⟨w.property,rfl⟩
      · exact Or.inr ⟨w.property,rfl⟩
  · rintro (⟨hu,rfl⟩ | ⟨hv,rfl⟩)
    · refine ⟨⟨u,hu⟩,?_⟩
      rcases P.endpoints u hu with ⟨hh,ht⟩ | ⟨ht,hh⟩
      · exact Or.inr ⟨ht.symm,hh.symm⟩
      · exact Or.inl ⟨ht.symm,hh.symm⟩
    · refine ⟨⟨v,hv⟩,?_⟩
      rcases P.endpoints v hv with ⟨hh,ht⟩ | ⟨ht,hh⟩
      · exact Or.inl ⟨ht.symm,hh.symm⟩
      · exact Or.inr ⟨ht.symm,hh.symm⟩

lemma graph_reachable_root (v : Vertex n) : (edgeGraph P.treeEdges).Reachable v T.root := by
  induction v using (measure T.level).wf.induction with
  | h v ih =>
    by_cases hv : v = T.root
    · subst v; exact .rfl
    · exact ((P.graph_adj v (T.parent v)).mpr (T.parent_adj v hv)).reachable.trans
        (ih (T.parent v) (T.parent_lower v hv))

lemma graph_connected : (edgeGraph P.treeEdges).Connected where
  preconnected u v := (P.graph_reachable_root u).trans (P.graph_reachable_root v).symm
  nonempty := ⟨T.root⟩

lemma card_treeEdges : P.treeEdges.card + 1 = Fintype.card (Vertex n) := by
  simp only [treeEdges,Finset.card_image_of_injective _ P.edge_injective,Finset.card_univ]
  have h := Fintype.card_subtype_compl (fun v : Vertex n => v = T.root)
  have hc : Fintype.card {v : Vertex n // v = T.root} = 1 := by simp
  rw [hc] at h
  change Fintype.card {v : Vertex n // v ≠ T.root} = _ at h
  have hp : 0 < Fintype.card (Vertex n) := Fintype.card_pos_iff.mpr ⟨T.root⟩
  omega

lemma graph_isTree : (edgeGraph P.treeEdges).IsTree := by
  rw [SimpleGraph.isTree_iff_connected_and_card]
  exact ⟨P.graph_connected,by rw [edgeGraph_card,Nat.card_eq_fintype_card]; exact P.card_treeEdges⟩

end ParentEdges

end

end WitnessedSeparation.Grid


section

namespace WitnessedChoice.BGS

noncomputable section

open Classical WitnessedSeparation WitnessedSeparation.Hereditary QuotedTerm

namespace QuotedFormula

variable {A V : Type} [Fintype A] [Fintype V] {k : ℕ}

lemma meaning_leastVertex (S : Input A) (env : Fin k → HF A)
    (ats VT R vt : QuotedTerm k) (code : V → HF A) (hc : Function.Injective code)
    (G : SimpleGraph V) (hG : G.Connected) (α : Fin 4 → V) (v : V)
    (hα : ats.meaning S env = tupleCode (List.ofFn (code ∘ α)))
    (hV : VT.meaning S env = ofFinset (Finset.univ.image code))
    (hR : R.meaning S env = ofFinset ((BFS.closure G (Fintype.card A)).image (distanceCode code)))
    (hv : vt.meaning S env = code v) (hcard : Fintype.card V ≤ Fintype.card A) :
    (leastVertex ats VT R vt).meaning S env ↔ v = α 0 := by
  simp only [leastVertex,meaning_and,meaning_mem,hv,hV,elements_ofFinset,
    Finset.mem_image,Finset.mem_univ,true_and,hc.eq_iff,exists_eq,true_and,
    meaning_allIn,forall_exists_index,forall_apply_eq_imp_iff,meaning_neg]
  have hm (w : V) : (vertexLt ats.up R.up (var 0) vt.up).meaning S (Fin.cons (code w) env) ↔
      AnchoredTree.key G α w < AnchoredTree.key G α v := by
    apply meaning_vertexLt S _ _ _ _ _ code hc G hG α w v
    all_goals first | assumption | rfl
  simpa only [hm] using AnchoredTree.least_iff_root G hG α v

end QuotedFormula

namespace QuotedTerm

variable {A V : Type} [Fintype A] [Fintype V] {k : ℕ}

lemma meaning_root (S : Input A) (env : Fin k → HF A)
    (ats VT R : QuotedTerm k) (code : V → HF A) (hc : Function.Injective code)
    (G : SimpleGraph V) (hG : G.Connected) (α : Fin 4 → V)
    (hα : ats.meaning S env = tupleCode (List.ofFn (code ∘ α)))
    (hV : VT.meaning S env = ofFinset (Finset.univ.image code))
    (hR : R.meaning S env = ofFinset ((BFS.closure G (Fintype.card A)).image (distanceCode code)))
    (hcard : Fintype.card V ≤ Fintype.card A) :
    (root ats VT R).meaning S env = code (α 0) := by
  have hm (v : V) : (QuotedFormula.leastVertex ats.up VT.up R.up (var 0)).meaning S
      (Fin.cons (code v) env) ↔ v = α 0 := by
    apply QuotedFormula.meaning_leastVertex S _ _ _ _ _ code hc G hG α v
    all_goals first | assumption | rfl
  simp only [root,meaning_unique,meaning_filter,hV,elements_ofFinset]
  have hf : (Finset.univ.image code).filter (fun z =>
      (QuotedFormula.leastVertex ats.up VT.up R.up (var 0)).meaning S (Fin.cons z env)) =
      {code (α 0)} := by
    ext z
    simp only [Finset.mem_filter,Finset.mem_image,Finset.mem_univ,true_and,Finset.mem_singleton]
    constructor
    · rintro ⟨⟨v,rfl⟩,hv⟩
      rw [hm] at hv
      rw [hv]
    · rintro rfl
      exact ⟨⟨α 0,rfl⟩,(hm _).mpr rfl⟩
  rw [hf]
  exact uniqueHF_singleton _

end QuotedTerm

end

end WitnessedChoice.BGS

namespace WitnessedSeparation.Grid

noncomputable section

open Classical WitnessedChoice WitnessedChoice.BGS Hereditary

variable {n : ℕ} {b : Vertex n → Scalar}

def anchoredTree (α : Fin 4 → Vertex n) : TreeTest.RootedTree (Vertex n) :=
  AnchoredTree.rooted (boxGraph n) (boxGraph_connected n) α

def anchoredParents (α : Fin 4 → Vertex n) : ParentEdges (anchoredTree α) where
  edge v hv := ((boxGraph_adj_iff v ((anchoredTree α).parent v)).mp
    (AnchoredTree.parent_property (boxGraph n) (boxGraph_connected n) α v hv).1.1).choose
  endpoints v hv := by
    have h := ((boxGraph_adj_iff v ((anchoredTree α).parent v)).mp
      (AnchoredTree.parent_property (boxGraph n) (boxGraph_connected n) α v hv).1.1).choose_spec
    rcases h with ⟨h,h'⟩ | ⟨h',h⟩
    · exact Or.inr ⟨h.symm,h'.symm⟩
    · exact Or.inl ⟨h.symm,h'.symm⟩

namespace QuotedGrid

open QuotedTerm QuotedFormula

variable {k : ℕ}

lemma meaning_incident (env : Fin k → HF (Atom b)) (vt et : QuotedTerm k)
    (u : Vertex n) (e : Edge n) (hu : vt.meaning (atomInput b) env = vertexCode b u)
    (he : et.meaning (atomInput b) env = edgeCode b e) (hn : 1 ≤ n) :
    (QuotedFormula.incident vt et).meaning (atomInput b) env ↔ incident u e := by
  rw [QuotedFormula.meaning_incident,hu,he]
  exact blockIncident_grid hn u e

lemma meaning_adjacent (env : Fin k → HF (Atom b)) (Et ut vt : QuotedTerm k)
    (D : Finset (Edge n)) (u v : Vertex n)
    (hE : Et.meaning (atomInput b) env = ofFinset (D.image (edgeCode b)))
    (hu : ut.meaning (atomInput b) env = vertexCode b u)
    (hv : vt.meaning (atomInput b) env = vertexCode b v) (hn : 1 ≤ n) :
    (adjacent Et ut vt).meaning (atomInput b) env ↔ (edgeGraph D).Adj u v := by
  rw [QuotedFormula.meaning_adjacent,hE,hu,hv]
  exact blockAdjacent_edges hn D u v

lemma meaning_parentEligible (env : Fin k → HF (Atom b)) (Et R rt vt wt : QuotedTerm k)
    (r v w : Vertex n)
    (hE : Et.meaning (atomInput b) env = ofFinset (Finset.univ.image (edgeCode b)))
    (hR : R.meaning (atomInput b) env = ofFinset
      ((BFS.closure (boxGraph n) (Fintype.card (Atom b))).image (distanceCode (vertexCode b))))
    (hr : rt.meaning (atomInput b) env = vertexCode b r)
    (hv : vt.meaning (atomInput b) env = vertexCode b v)
    (hw : wt.meaning (atomInput b) env = vertexCode b w) (hn : 1 ≤ n) :
    (parentEligible Et R rt vt wt).meaning (atomInput b) env ↔ AnchoredTree.Eligible (boxGraph n) r v w := by
  have hd (u : Vertex n) (ut : QuotedTerm k) (hu : ut.meaning (atomInput b) env = vertexCode b u) :=
    QuotedTerm.meaning_distanceAt (atomInput b) env R rt ut (vertexCode b) (vertexCode_injective hn)
      (boxGraph n) (boxGraph_connected n) r u hR hr hu (vertex_card_le_atoms hn)
  rw [parentEligible,meaning_and,meaning_adjacent env Et vt wt _ v w hE hv hw hn,edgeGraph_univ]
  simp only [meaning_eq,meaning_successor,hd w wt hw,hd v vt hv]
  change ((boxGraph n).Adj v w ∧ ordinal ((boxGraph n).dist r w + 1) = ordinal ((boxGraph n).dist r v)) ↔ _
  rw [ordinal_injective.eq_iff]
  rfl

lemma meaning_parent (env : Fin k → HF (Atom b)) (ats VT Et R rt vt wt : QuotedTerm k)
    (α : Fin 4 → Vertex n) (v w : Vertex n) (hres : AnchoredTree.Resolving (boxGraph n) α)
    (hα : ats.meaning (atomInput b) env = tupleCode (List.ofFn (vertexCode b ∘ α)))
    (hV : VT.meaning (atomInput b) env = ofFinset (Finset.univ.image (vertexCode b)))
    (hE : Et.meaning (atomInput b) env = ofFinset (Finset.univ.image (edgeCode b)))
    (hR : R.meaning (atomInput b) env = ofFinset
      ((BFS.closure (boxGraph n) (Fintype.card (Atom b))).image (distanceCode (vertexCode b))))
    (hr : rt.meaning (atomInput b) env = vertexCode b (α 0))
    (hv : vt.meaning (atomInput b) env = vertexCode b v)
    (hw : wt.meaning (atomInput b) env = vertexCode b w) (hn : 1 ≤ n) :
    (QuotedFormula.parent ats VT Et R rt vt wt).meaning (atomInput b) env ↔
      v ≠ α 0 ∧ (anchoredTree α).parent v = w := by
  have hel (z : Vertex n) : (parentEligible Et.up R.up rt.up vt.up (var 0)).meaning
      (atomInput b) (Fin.cons (vertexCode b z) env) ↔ AnchoredTree.Eligible (boxGraph n) (α 0) v z := by
    apply meaning_parentEligible _ _ _ _ _ _ _ _ _ _ _ _ _ _ hn
    all_goals first | assumption | exact vertex_card_le_atoms hn | rfl
  have hlt (z : Vertex n) : (vertexLt ats.up R.up (var 0) wt.up).meaning
      (atomInput b) (Fin.cons (vertexCode b z) env) ↔
      AnchoredTree.key (boxGraph n) α z < AnchoredTree.key (boxGraph n) α w := by
    apply QuotedFormula.meaning_vertexLt _ _ _ _ _ _ (vertexCode b) (vertexCode_injective hn)
      (boxGraph n) (boxGraph_connected n) α z w
    all_goals first | assumption | exact vertex_card_le_atoms hn | rfl
  simp only [QuotedFormula.parent,meaning_and,meaning_parentEligible env Et R rt vt wt _ _ _ hE hR hr hv hw hn,
    meaning_allIn,hV,elements_ofFinset,Finset.mem_image,Finset.mem_univ,true_and,
    forall_exists_index,forall_apply_eq_imp_iff,meaning_imp,meaning_neg,hel,hlt]
  exact AnchoredTree.parent_iff (boxGraph n) (boxGraph_connected n) α hres v w

end QuotedGrid

end

end WitnessedSeparation.Grid

end


namespace WitnessedSeparation.Grid

noncomputable section

open Classical SimpleGraph

variable {n : ℕ}

lemma endpoints_iff_incident (u v : Vertex n) (e : Edge n) (hne : u ≠ v) :
    ((u = tail e ∧ v = head e) ∨ (v = tail e ∧ u = head e)) ↔
      incident u e ∧ incident v e := by
  simp only [incident]
  constructor
  · rintro (⟨hu,hv⟩|⟨hv,hu⟩)
    · exact ⟨Or.inr hu.symm,Or.inl hv.symm⟩
    · exact ⟨Or.inl hu.symm,Or.inr hv.symm⟩
  · rintro ⟨(hu|hu),(hv|hv)⟩
    · exact (hne (hu.symm.trans hv)).elim
    · exact Or.inr ⟨hv.symm,hu.symm⟩
    · exact Or.inl ⟨hu.symm,hv.symm⟩
    · exact (hne (hu.symm.trans hv)).elim

lemma edge_eq_of_common_incidents (u v : Vertex n) (e f : Edge n) (hne : u ≠ v)
    (heu : incident u e) (hev : incident v e) (hfu : incident u f) (hfv : incident v f) : e=f := by
  have he := (endpoints_iff_incident u v e hne).mpr ⟨heu,hev⟩
  have hf := (endpoints_iff_incident u v f hne).mpr ⟨hfu,hfv⟩
  apply edge_eq_of_endpoints
  rcases he with ⟨he₁,he₂⟩|⟨he₂,he₁⟩
  all_goals rcases hf with ⟨hf₁,hf₂⟩|⟨hf₂,hf₁⟩
  · exact Or.inl ⟨he₁.symm.trans hf₁,he₂.symm.trans hf₂⟩
  · exact Or.inr ⟨he₁.symm.trans hf₁,he₂.symm.trans hf₂⟩
  · exact Or.inr ⟨he₂.symm.trans hf₂,he₁.symm.trans hf₁⟩
  · exact Or.inl ⟨he₂.symm.trans hf₂,he₁.symm.trans hf₁⟩

lemma edge_on_face (f : Face n) (i j : Fin 4) (e : Edge n) (hij : AdjacentIndex i j)
    (hi : incident (faceCorner f i) e) (hj : incident (faceCorner f j) e) : cycle f e ≠ 0 := by
  rcases hij with rfl|rfl
  · have hn : faceCorner f i ≠ faceCorner f (i+1) := by
      intro h
      have hh := faceCorner_index_injective f h
      have hbad : ∀ i : Fin 4, i ≠ i+1 := by decide
      exact hbad i hh
    have he := edge_eq_of_common_incidents _ _ e (faceSide f i) hn hi hj
      ((incident_faceSide f i _).mpr (Or.inl rfl))
      ((incident_faceSide f i _).mpr (Or.inr rfl))
    rw [he]
    exact cycle_faceSide f i
  · have hn : faceCorner f j ≠ faceCorner f (j+1) := by
      intro h
      have hh := faceCorner_index_injective f h
      have hbad : ∀ i : Fin 4, i ≠ i+1 := by decide
      exact hbad j hh
    have he := edge_eq_of_common_incidents _ _ e (faceSide f j) hn hj hi
      ((incident_faceSide f j _).mpr (Or.inl rfl))
      ((incident_faceSide f j _).mpr (Or.inr rfl))
    rw [he]
    exact cycle_faceSide f j

lemma indexed_cycle_incident (v : Fin 4 → Vertex n) (e : Fin 4 → Edge n)
    (he : ∀ i, (v i = tail (e i) ∧ v (i+1) = head (e i)) ∨
      (v (i+1) = tail (e i) ∧ v i = head (e i))) (i : Fin 4) :
    incident (v i) (e i) ∧ incident (v (i+1)) (e i) := by
  rcases he i with ⟨h,h'⟩|⟨h',h⟩
  · exact ⟨Or.inr h.symm,Or.inl h'.symm⟩
  · exact ⟨Or.inl h.symm,Or.inr h'.symm⟩

theorem indexed_fourcycle_is_face (v : Fin 4 → Vertex n) (e : Fin 4 → Edge n)
    (hv : Function.Injective v) (heinj : Function.Injective e)
    (he : ∀ i, (v i = tail (e i) ∧ v (i+1) = head (e i)) ∨
      (v (i+1) = tail (e i) ∧ v i = head (e i))) :
    ∃ f : Face n, ∀ i, cycle f (e i) ≠ 0 := by
  have hi := indexed_cycle_incident v e he
  obtain ⟨f,hf₀,hf₁⟩ := incident_perpendicular_face (v 1) (e 0) (e 1)
    (hi 0).2 (hi 1).1 (square_consecutive_perpendicular v e hv he)
  obtain ⟨i,hi₀⟩ := support_cycle f (e 0) hf₀
  obtain ⟨j,hj₁⟩ := support_cycle f (e 1) hf₁
  have hij : i ≠ j := by
    intro h
    have hh : e 0=e 1 := hi₀.symm.trans (h ▸ hj₁)
    exact (by decide : (0 : Fin 4) ≠ 1) (heinj hh)
  obtain ⟨k,h₀,h₂⟩ := face_chain_opposite f i j (v 0) (v 1) (v 2) hij
    (fun h => (by decide : (0 : Fin 4) ≠ 1) (hv h))
    (fun h => (by decide : (1 : Fin 4) ≠ 2) (hv h))
    (hi₀ ▸ (hi 0).1) (hi₀ ▸ (hi 0).2) (hj₁ ▸ (hi 1).1) (hj₁ ▸ (hi 1).2)
  have hadj (i : Fin 4) : (boxGraph n).Adj (v i) (v (i+1)) :=
    (boxGraph_adj_iff _ _).mpr ⟨e i,he i⟩
  have h₁ : v 1=faceCorner f (k+1) ∨ v 1=faceCorner f (k+3) :=
    square_common_neighbors f k (v 1) (h₀ ▸ hadj 0) (h₂ ▸ (hadj 1).symm)
  have h₃ : v 3=faceCorner f (k+1) ∨ v 3=faceCorner f (k+3) :=
    square_common_neighbors f k (v 3) (h₀ ▸ (hadj 3).symm) (h₂ ▸ hadj 2)
  have hv₁₃ : v 1 ≠ v 3 := fun h => (by decide : (1 : Fin 4) ≠ 3) (hv h)
  have sufficient (J : Fin 4 → Fin 4) (hJ : ∀ i, v i = faceCorner f (J i))
      (hA : ∀ i, AdjacentIndex (J i) (J (i+1))) : ∀ i, cycle f (e i) ≠ 0 := by
    intro i
    exact edge_on_face f _ _ (e i) (hA i) (hJ i ▸ (hi i).1) (hJ (i+1) ▸ (hi i).2)
  refine ⟨f,?_⟩
  rcases h₁ with h₁|h₁
  all_goals rcases h₃ with h₃|h₃
  · exact (hv₁₃ (h₁.trans h₃.symm)).elim
  · refine sufficient ![k,k+1,k+2,k+3] ?_ ?_
    · intro i; fin_cases i <;> assumption
    · have h : ∀ k i : Fin 4, AdjacentIndex (![k,k+1,k+2,k+3] i)
          (![k,k+1,k+2,k+3] (i+1)) := by unfold AdjacentIndex; decide
      exact h k
  · refine sufficient ![k,k+3,k+2,k+1] ?_ ?_
    · intro i; fin_cases i <;> assumption
    · have h : ∀ k i : Fin 4, AdjacentIndex (![k,k+3,k+2,k+1] i)
          (![k,k+3,k+2,k+1] (i+1)) := by unfold AdjacentIndex; decide
      exact h k
  · exact (hv₁₃ (h₁.trans h₃.symm)).elim

end





noncomputable section

open Classical Support

variable {n : ℕ} {b : Vertex n → Scalar}

structure CycleFrame (n : ℕ) where
  vertex : Fin 4 → Vertex n
  edge : Fin 4 → Edge n
  vertex_injective : Function.Injective vertex
  edge_injective : Function.Injective edge
  endpoints : ∀ i, (vertex i = tail (edge i) ∧ vertex (i+1) = head (edge i)) ∨
    (vertex (i+1) = tail (edge i) ∧ vertex i = head (edge i))

namespace CycleFrame

variable (C : CycleFrame n)

def face : Face n := (indexed_fourcycle_is_face C.vertex C.edge C.vertex_injective C.edge_injective C.endpoints).choose

lemma on_face (i : Fin 4) : cycle C.face (C.edge i) ≠ 0 :=
  (indexed_fourcycle_is_face C.vertex C.edge C.vertex_injective C.edge_injective C.endpoints).choose_spec i

lemma incident_ends (i : Fin 4) : incident (C.vertex i) (C.edge i) ∧ incident (C.vertex (i+1)) (C.edge i) :=
  indexed_cycle_incident C.vertex C.edge C.endpoints i

lemma consecutive_axis_ne (i : Fin 4) : edgeAxis (C.edge i) ≠ edgeAxis (C.edge (i+1)) := by
  have hadd : Function.Injective (fun j : Fin 4 => i+j) := by
    have h : ∀ i j k : Fin 4, i+j=i+k → j=k := by decide
    exact h i
  have hh := square_consecutive_perpendicular (fun j => C.vertex (i+j)) (fun j => C.edge (i+j))
    (C.vertex_injective.comp hadd) (fun j => by simpa only [add_assoc] using C.endpoints (i+j))
  simpa only [add_zero] using hh

lemma adjacent_axis_ne (i j : Fin 4) (h : AdjacentIndex i j) : edgeAxis (C.edge i) ≠ edgeAxis (C.edge j) := by
  rcases h with rfl | rfl
  · exact C.consecutive_axis_ne i
  · exact (C.consecutive_axis_ne j).symm

lemma support_iff (e : Edge n) : cycle C.face e ≠ 0 ↔ ∃ i, e = C.edge i := by
  choose J hJ using fun i => support_cycle C.face (C.edge i) (C.on_face i)
  have hJi : Function.Injective J := by
    intro i j hh
    apply C.edge_injective
    exact (hJ i).symm.trans (hh ▸ hJ j)
  constructor
  · intro he
    obtain ⟨k,hk⟩ := support_cycle C.face e he
    obtain ⟨i,rfl⟩ := Finite.surjective_of_injective hJi k
    exact ⟨i,hk.symm.trans (hJ i)⟩
  · rintro ⟨i,rfl⟩
    exact C.on_face i

lemma face_unique (f : Face n) (hf : ∀ i, cycle f (C.edge i) ≠ 0) : C.face = f :=
  common_face_unique (C.edge 0) (C.edge 1) (C.consecutive_axis_ne 0)
    (C.on_face 0) (C.on_face 1) (hf 0) (hf 1)

def joint (i j : Fin 4) : Vertex n := if j=i+1 then C.vertex j else C.vertex i

lemma joint_incident (i j : Fin 4) (h : AdjacentIndex i j) :
    incident (C.joint i j) (C.edge i) ∧ incident (C.joint i j) (C.edge j) := by
  unfold joint
  split_ifs with he
  · subst j
    exact ⟨(C.incident_ends i).2,(C.incident_ends (i+1)).1⟩
  · have hi : i=j+1 := h.resolve_left he
    subst i
    exact ⟨(C.incident_ends (j+1)).1,(C.incident_ends j).2⟩

def Across (i j : Fin 4) (s : LocalGroup (C.edge i)) (t : LocalGroup (C.edge j)) : Prop :=
  ∃ hi : incident (C.joint i j) (C.edge i), ∃ hj : incident (C.joint i j) (C.edge j),
    ∃ c : Configuration b (C.joint i j), c.state ⟨C.edge i,hi⟩ = s ∧ c.state ⟨C.edge j,hj⟩ = t

lemma across_iff (hn : 1 ≤ n) (i j : Fin 4) (h : AdjacentIndex i j)
    (s : LocalGroup (C.edge i)) (t : LocalGroup (C.edge j)) :
    C.Across (b := b) i j s t ↔ s.face ⟨C.face,C.on_face i⟩ = t.face ⟨C.face,C.on_face j⟩ := by
  constructor
  · rintro ⟨hi,hj,c,hs,ht⟩
    simpa only [hs,ht] using c.compatible ⟨_,hi⟩ ⟨_,hj⟩ C.face (C.on_face i) (C.on_face j)
  · intro hs
    obtain ⟨hi,hj⟩ := C.joint_incident i j h
    have he : (⟨C.edge i,hi⟩ : IncidentEdges (C.joint i j)) ≠ ⟨C.edge j,hj⟩ := by
      intro hh
      exact C.adjacent_axis_ne i j h (congrArg (edgeAxis ∘ Subtype.val) hh)
    obtain ⟨c,hc,hc'⟩ := exists_configuration_two (b := b) hn ⟨_,hi⟩ ⟨_,hj⟩ he s t (by
      intro f hfi hfj
      have hf := common_face_unique _ _ (C.adjacent_axis_ne i j h) (C.on_face i) (C.on_face j) hfi hfj
      subst f
      exact hs)
    exact ⟨hi,hj,c,hc,hc'⟩

def Match (i j : Fin 4) (s : LocalGroup (C.edge i)) (t : LocalGroup (C.edge j)) : Prop :=
  if AdjacentIndex i j then C.Across (b := b) i j s t else
    ∃ q : LocalGroup (C.edge (i+1)), C.Across (b := b) i (i+1) s q ∧ C.Across (b := b) j (i+1) t q

lemma match_iff (hn : 1 ≤ n) (i j : Fin 4) (s : LocalGroup (C.edge i)) (t : LocalGroup (C.edge j)) :
    C.Match (b := b) i j s t ↔ s.face ⟨C.face,C.on_face i⟩ = t.face ⟨C.face,C.on_face j⟩ := by
  unfold Match
  split_ifs with h
  · exact C.across_iff hn i j h s t
  · simp only [C.across_iff hn i (i+1) (index_next_adjacent i),
      C.across_iff hn j (i+1) (nonadjacent_next i j h)]
    constructor
    · rintro ⟨q,hs,ht⟩
      exact hs.trans ht.symm
    · intro he
      exact ⟨⟨fun _ => s.face ⟨C.face,C.on_face i⟩,0⟩,rfl,he.symm⟩

end CycleFrame

def standardFrame (f : Face n) : CycleFrame n where
  vertex := faceCorner f
  edge := faceSide f
  vertex_injective := faceCorner_index_injective f
  edge_injective := faceSide_injective_index f
  endpoints i := by
    have hi := (incident_faceSide f i (faceCorner f i)).mpr (Or.inl rfl)
    have hj := (incident_faceSide f i (faceCorner f (i+1))).mpr (Or.inr rfl)
    have hne : faceCorner f i ≠ faceCorner f (i+1) := by
      intro hh
      have he := faceCorner_index_injective f hh
      have hbad : ∀ i : Fin 4, i ≠ i+1 := by decide
      exact hbad i he
    rcases hi with hi | hi <;> rcases hj with hj | hj
    · exact (hne (hi.symm.trans hj)).elim
    · exact Or.inr ⟨hj.symm,hi.symm⟩
    · exact Or.inl ⟨hi.symm,hj.symm⟩
    · exact (hne (hi.symm.trans hj)).elim

@[simp] lemma standardFrame_face (f : Face n) : (standardFrame f).face = f :=
  (standardFrame f).face_unique f (cycle_faceSide f)

end

end WitnessedSeparation.Grid

end OAI
