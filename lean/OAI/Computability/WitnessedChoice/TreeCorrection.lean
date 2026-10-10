import OAI.Computability.WitnessedChoice.CycleTranslation

namespace OAI


namespace WitnessedSeparation.Grid

noncomputable section

open Classical WitnessedChoice WitnessedChoice.BGS WitnessedChoice.TreeTest Hereditary RelationPools

variable {n : ℕ} {b : Vertex n → Scalar}

def edgeActionRelation (g : BoxGroup n) : Relation (Atom b) :=
  Finset.univ.image fun r : Σ e : Edge n, LocalGroup e =>
    ((Sum.inl r : Atom b),actionPerm g (.inl r))

lemma mem_edgeActionRelation (g : BoxGroup n) (a c : Atom b) :
    (a,c) ∈ edgeActionRelation g ↔
      ∃ (e : Edge n) (s : LocalGroup e), a = .inl ⟨e,s⟩ ∧ c = .inl ⟨e,restrictGroup e g*s⟩ := by
  simp only [edgeActionRelation,Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨⟨e,s⟩,h⟩
    cases h
    exact ⟨e,s,rfl,rfl⟩
  · rintro ⟨e,s,rfl,rfl⟩
    exact ⟨⟨e,s⟩,rfl⟩

namespace QuotedGrid

open QuotedTerm QuotedFormula SourceSyntax

variable {k : ℕ} {T : RootedTree (Vertex n)}

lemma meaning_cycleY_move (env : Fin k → HF (Atom b)) (F R Γ ot ht st tt : QuotedTerm k)
    (P : ParentEdges T) (e : Edge n) (he : e ∉ P.treeEdges) (h : Edge n) (s t : LocalGroup h)
    (hF : ∀ z, z ∈ elements (F.meaning (atomInput b) env) ↔ ∃ C : CycleFrame n, frameCode b C = z)
    (hR : R.meaning (atomInput b) env = distancesCode b (boxGraph n))
    (hΓ : Γ.meaning (atomInput b) env = traversalCode b P.treeEdges e (tail e) (head e))
    (ho : ot.meaning (atomInput b) env = vertexCode b originVertex)
    (hh : ht.meaning (atomInput b) env = edgeCode b h)
    (hs : st.meaning (atomInput b) env = atom (.inl ⟨h,s⟩))
    (ht' : tt.meaning (atomInput b) env = atom (.inl ⟨h,t⟩)) (hn : 1 ≤ n) :
    (((traversalEdge Γ ht).neg.and (eq st tt)).or
      ((traversalEdge Γ ht).and ((baseEq F ht st tt).and (directedZ R Γ ot ht st tt)))).meaning (atomInput b) env ↔
      t = restrictGroup h (⟨0,P.flow e 1⟩ : BoxGroup n)*s := by
  rw [meaning_or,meaning_and,meaning_neg,meaning_and,meaning_and,
    meaning_traversalEdge env Γ ht P.treeEdges e (tail e) (head e) h hΓ hh,
    P.traverses_iff_nonzero e he h,
    meaning_baseEq env F ht st tt h s t hF hh hs ht' hn,
    meaning_directedZ env R Γ ot ht st tt P.treeEdges e (tail e) (head e) originVertex h s t
      hR hΓ ho hh hs ht' hn,
    P.directed_flow_iff e he h (s⁻¹*t).flow,meaning_eq,hs,ht']
  have ha : atom (Sum.inl ⟨h,s⟩ : Atom b) = atom (.inl ⟨h,t⟩) ↔ s=t := by
    simp only [atom_injective.eq_iff,Sum.inl.injEq,Sigma.mk.inj_iff,heq_eq_eq,true_and]
  rw [ha]
  change _ ↔ t = (⟨0,(P.flow e 1).val h⟩ : LocalGroup h)*s
  rw [local_central_iff]
  by_cases hz : (P.flow e 1).val h = 0
  · simp only [hz,not_false_eq_true,true_and,ne_eq,not_true_eq_false,false_and,or_false]
    constructor
    · rintro rfl
      simp
    · rintro ⟨hf,htf⟩
      have hh := (local_central_iff h s t 0).mpr ⟨hf,htf⟩
      simpa only [show (⟨0,0⟩ : LocalGroup h)=1 from rfl,one_mul] using hh.symm
  · tauto

lemma exists_edgeCode (Q : HF (Atom b) → Prop) :
    (∃ z ∈ elements (ofFinset (Finset.univ.image (edgeCode b))), Q z) ↔
      ∃ e : Edge n, Q (edgeCode b e) := by
  simp only [elements_ofFinset,Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨z,⟨e,rfl⟩,h⟩
    exact ⟨e,h⟩
  · rintro ⟨e,h⟩
    exact ⟨_,⟨e,rfl⟩,h⟩

lemma meaning_cycleY (env : Fin k → HF (Atom b)) (E F R Γ ot : QuotedTerm k)
    (P : ParentEdges T) (e : Edge n) (he : e ∉ P.treeEdges)
    (hE : E.meaning (atomInput b) env = ofFinset (Finset.univ.image (edgeCode b)))
    (hF : ∀ z, z ∈ elements (F.meaning (atomInput b) env) ↔ ∃ C : CycleFrame n, frameCode b C = z)
    (hR : R.meaning (atomInput b) env = distancesCode b (boxGraph n))
    (hΓ : Γ.meaning (atomInput b) env = traversalCode b P.treeEdges e (tail e) (head e))
    (ho : ot.meaning (atomInput b) env = vertexCode b originVertex) (hn : 1 ≤ n) :
    (cycleY E F R Γ ot).meaning (atomInput b) env =
      relationCode (edgeActionRelation (b := b) (⟨0,P.flow e 1⟩ : BoxGroup n)) := by
  rw [cycleY,meaning_relation]
  apply congrArg relationCode
  ext ⟨a,c⟩
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,meaning_existsIn,QuotedTerm.meaning_up,
    hE,exists_edgeCode,
    meaning_allList,List.mem_cons,List.mem_nil_iff,forall_eq_or_imp,forall_false,implies_true,and_true,
    meaning_mem,meaning_var,Fin.cons_zero,Fin.cons_one,fin_cons_two,mem_edgeCode_iff,
    mem_edgeActionRelation]
  constructor
  · rintro ⟨h,⟨s,hs⟩,⟨t,ht⟩,hm⟩
    have hs' := atom_injective hs
    have ht' := atom_injective ht
    subst a
    subst c
    have hmove := (meaning_cycleY_move
      (Fin.cons (edgeCode b h) (Fin.cons (atom (.inl ⟨h,t⟩)) (Fin.cons (atom (.inl ⟨h,s⟩)) env)))
      F.up.up.up R.up.up.up Γ.up.up.up ot.up.up.up (var 0) (var 2) (var 1)
      P e he h s t hF hR hΓ ho rfl rfl rfl hn).mp hm
    exact ⟨h,s,rfl,congrArg (fun t : LocalGroup h => (Sum.inl ⟨h,t⟩ : Atom b)) hmove⟩
  · rintro ⟨h,s,rfl,rfl⟩
    refine ⟨h,⟨s,rfl⟩,⟨restrictGroup h (⟨0,P.flow e 1⟩ : BoxGroup n)*s,rfl⟩,?_⟩
    exact (meaning_cycleY_move
      (Fin.cons (edgeCode b h) (Fin.cons (atom (.inl ⟨h,restrictGroup h (⟨0,P.flow e 1⟩ : BoxGroup n)*s⟩))
        (Fin.cons (atom (.inl ⟨h,s⟩)) env)))
      F.up.up.up R.up.up.up Γ.up.up.up ot.up.up.up (var 0) (var 2) (var 1)
      P e he h s _ hF hR hΓ ho rfl rfl rfl hn).mpr rfl

end QuotedGrid

end





noncomputable section

open Classical WitnessedChoice WitnessedChoice.BGS WitnessedChoice.TreeTest Hereditary RelationPools

variable {n : ℕ} {b : Vertex n → Scalar}

def configActionRelation (g : BoxGroup n) : Relation (Atom b) :=
  Finset.univ.image fun r : Σ v : Vertex n, Configuration b v =>
    ((Sum.inr r : Atom b),actionPerm g (.inr r))

lemma mem_configActionRelation (g : BoxGroup n) (a c : Atom b) :
    (a,c) ∈ configActionRelation g ↔
      ∃ (v : Vertex n) (s : Configuration b v), a = .inr ⟨v,s⟩ ∧ c = .inr ⟨v,actConfiguration g s⟩ := by
  simp only [configActionRelation,Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨⟨v,s⟩,h⟩
    cases h
    exact ⟨v,s,rfl,rfl⟩
  · rintro ⟨v,s,rfl,rfl⟩
    exact ⟨⟨v,s⟩,rfl⟩

lemma edge_config_union (g : BoxGroup n) :
    edgeActionRelation (b := b) g ∪ configActionRelation g = graph (actionPerm g) := by
  ext ⟨a,c⟩
  simp only [Finset.mem_union,mem_edgeActionRelation,mem_configActionRelation,mem_graph]
  cases a with
  | inl r =>
    rcases r with ⟨e,s⟩
    simp only [Sum.inl.injEq,Sum.inl_ne_inr,false_and,exists_false,or_false]
    constructor
    · rintro ⟨d,t,h,rfl⟩
      cases h
      rfl
    · intro h
      exact ⟨e,s,rfl,h.symm⟩
  | inr r =>
    rcases r with ⟨v,s⟩
    simp only [Sum.inr.injEq,Sum.inr_ne_inl,false_and,exists_false,false_or]
    constructor
    · rintro ⟨w,t,h,rfl⟩
      cases h
      rfl
    · intro h
      exact ⟨v,s,rfl,h.symm⟩

namespace QuotedGrid

open QuotedTerm QuotedFormula SourceSyntax

variable {k : ℕ}

lemma exists_vertexBlockCode (Q : HF (Atom b) → Prop) :
    (∃ z ∈ elements (ofFinset (Finset.univ.image (vertexCode b))), Q z) ↔
      ∃ v : Vertex n, Q (vertexCode b v) := by
  simp only [elements_ofFinset,Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨z,⟨v,rfl⟩,h⟩
    exact ⟨v,h⟩
  · rintro ⟨v,h⟩
    exact ⟨_,⟨v,rfl⟩,h⟩

lemma all_edgeBlockCode (Q : HF (Atom b) → Prop) :
    (∀ z ∈ elements (ofFinset (Finset.univ.image (edgeCode b))), Q z) ↔
      ∀ e : Edge n, Q (edgeCode b e) := by
  simp only [elements_ofFinset,Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · intro h e
    exact h _ ⟨e,rfl⟩
  · rintro h z ⟨e,rfl⟩
    exact h e

lemma pair_atoms_relationCode (r : Relation (Atom b)) (a c : Atom b) :
    Hereditary.pair (atom a) (atom c) ∈ elements (relationCode r) ↔ (a,c) ∈ r :=
  mem_elements_relationCode r a c

lemma meaning_cycleX (env : Fin k → HF (Atom b)) (V E cY : QuotedTerm k) (g : BoxGroup n)
    (hV : V.meaning (atomInput b) env = ofFinset (Finset.univ.image (vertexCode b)))
    (hE : E.meaning (atomInput b) env = ofFinset (Finset.univ.image (edgeCode b)))
    (hY : cY.meaning (atomInput b) env = relationCode (edgeActionRelation g)) (hn : 1 ≤ n) :
    (cycleX V E cY).meaning (atomInput b) env = relationCode (configActionRelation g) := by
  rw [cycleX,meaning_relation]
  apply congrArg relationCode
  ext ⟨a,c⟩
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,meaning_existsIn,QuotedTerm.meaning_up,
    hV,exists_vertexBlockCode,meaning_allList,List.mem_cons,List.mem_nil_iff,forall_eq_or_imp,
    forall_false,implies_true,and_true,meaning_mem,meaning_var,Fin.cons_zero,Fin.cons_one,fin_cons_two,
    mem_vertexCode_iff,mem_configActionRelation]
  constructor
  · rintro ⟨v,⟨s,hs⟩,⟨t,ht⟩,hm⟩
    have hs' := atom_injective hs
    have ht' := atom_injective ht
    subst a
    subst c
    refine ⟨v,s,rfl,?_⟩
    apply congrArg (fun t : Configuration b v => (Sum.inr ⟨v,t⟩ : Atom b))
    apply Configuration.ext
    intro e
    simp only [meaning_allIn,QuotedTerm.meaning_up,hE,all_edgeBlockCode] at hm
    have hh := hm e.val
    rw [meaning_imp,meaning_incident _ _ _ v e.val rfl rfl hn] at hh
    have he := hh e.property
    simp only [meaning_existsIn,meaning_var,Fin.cons_zero,Fin.cons_one,
      WitnessedSeparation.Grid.exists_edgeCode,meaning_allList,List.mem_cons,List.mem_nil_iff,
      forall_eq_or_imp,forall_false,implies_true,and_true,meaning_input,
      fin_cons_two,fin_cons_three,fin_cons_four,fin_cons_five,Fin.cons_zero,QuotedTerm.meaning_up,input_inc_iff,
      meaning_link,hY,pair_atoms_relationCode] at he
    obtain ⟨r,q,⟨hr,hsr⟩,⟨hq,htq⟩,hrel⟩ := he
    rw [mem_edgeActionRelation] at hrel
    obtain ⟨d,u,hru,hqu⟩ := hrel
    have hru' := Sum.inl.inj hru
    cases hru'
    have heq := eq_of_heq (Sigma.mk.inj (Sum.inl.inj hqu)).2
    change t.state e = restrictGroup e.val g*s.state e
    rw [hsr,htq,heq]
  · rintro ⟨v,s,rfl,rfl⟩
    refine ⟨v,⟨s,rfl⟩,⟨actConfiguration g s,rfl⟩,?_⟩
    simp only [meaning_allIn,QuotedTerm.meaning_up,hE,all_edgeBlockCode]
    intro e
    rw [meaning_imp,meaning_incident _ _ _ v e rfl rfl hn]
    intro he
    simp only [meaning_existsIn,meaning_var,Fin.cons_zero,Fin.cons_one,
      WitnessedSeparation.Grid.exists_edgeCode,meaning_allList,List.mem_cons,List.mem_nil_iff,
      forall_eq_or_imp,forall_false,implies_true,and_true,meaning_input,
      fin_cons_two,fin_cons_three,fin_cons_four,fin_cons_five,Fin.cons_zero,QuotedTerm.meaning_up,input_inc_iff,
      meaning_link,hY,pair_atoms_relationCode]
    exact ⟨s.state ⟨e,he⟩,restrictGroup e g*s.state ⟨e,he⟩,
      ⟨he,rfl⟩,⟨he,rfl⟩,(mem_edgeActionRelation _ _ _).mpr ⟨e,_,rfl,rfl⟩⟩

end QuotedGrid

end





noncomputable section

open Classical WitnessedChoice WitnessedChoice.BGS WitnessedChoice.TreeTest Hereditary

variable {n : ℕ}

def oppositeVertex : Vertex n := (Fin.last n,Fin.last n,Fin.last n)

lemma dist_opposite_tail (h : Edge n) :
    (boxGraph n).dist oppositeVertex (tail h) = (boxGraph n).dist oppositeVertex (head h) + 1 := by
  rcases h with ⟨i,j,k⟩ | (⟨i,j,k⟩ | ⟨i,j,k⟩)
  all_goals
    simp only [boxGraph_dist,oppositeVertex,tail,head,Fin.val_last,Fin.val_succ,Fin.val_castSucc]
    repeat' rw [Nat.dist_eq_sub_of_le_right (by omega)]
    omega

namespace ParentEdges

variable {T : RootedTree (Vertex n)} (P : ParentEdges T)

lemma flow_zero (e : Edge n) : P.flow e 0 = 0 := by
  apply Subtype.ext
  simp [flow,fundamental]

lemma flow_neg_one (e h : Edge n) : (P.flow e (-1)).val h = -(P.flow e 1).val h := by
  simp only [flow,fundamental,Pi.sub_apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul,
    neg_mul,one_mul,Pi.single_apply]
  split_ifs <;> ring

lemma traverses_iff_neg_nonzero (e : Edge n) (he : e ∉ P.treeEdges) (h : Edge n) :
    (∃ a c, Traverses P.treeEdges e (tail e) (head e) h a c) ↔ (P.flow e (-1)).val h ≠ 0 := by
  rw [P.flow_neg_one,neg_ne_zero,P.traverses_iff_nonzero e he h]

lemma opposite_directed_flow_iff (e : Edge n) (he : e ∉ P.treeEdges) (h : Edge n) (z : Scalar) :
    (∃ a c, Traverses P.treeEdges e (tail e) (head e) h a c ∧
      if (boxGraph n).dist oppositeVertex a < (boxGraph n).dist oppositeVertex c then z=1 else z=2) ↔
      (P.flow e (-1)).val h ≠ 0 ∧ z=(P.flow e (-1)).val h := by
  have hlt := dist_opposite_tail h
  have hm : (2 : Scalar) = -1 := by decide
  constructor
  · rintro ⟨a,c,htr,hz⟩
    have hne := (P.traverses_iff_neg_nonzero e he h).mp ⟨a,c,htr⟩
    refine ⟨hne,?_⟩
    rw [P.flow_neg_one]
    rcases P.traverses_endpoints htr with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · rw [(P.traverses_forward e he h).mp htr]
      simpa only [ite_eq_right (show ¬(boxGraph n).dist oppositeVertex (tail h) <
        (boxGraph n).dist oppositeVertex (head h) by omega),hm] using hz
    · rw [(P.traverses_reverse e he h).mp htr,neg_neg]
      simpa only [ite_eq_left (show (boxGraph n).dist oppositeVertex (head h) <
        (boxGraph n).dist oppositeVertex (tail h) by omega)] using hz
  · rintro ⟨hne,rfl⟩
    rw [P.flow_neg_one,neg_ne_zero] at hne
    rcases scalar_cases ((P.flow e 1).val h) with hz | hp | hm'
    · exact False.elim (hne hz)
    · refine ⟨tail h,head h,(P.traverses_forward e he h).mpr hp,?_⟩
      rw [ite_eq_right (by omega),P.flow_neg_one,hp,hm]
    · refine ⟨head h,tail h,(P.traverses_reverse e he h).mpr hm',?_⟩
      rw [ite_eq_left (by omega),P.flow_neg_one,hm',neg_neg]

end ParentEdges

end



noncomputable section

open Classical WitnessedChoice WitnessedChoice.BGS WitnessedChoice.TreeTest Hereditary RelationPools

variable {n : ℕ} {b : Vertex n → Scalar}

namespace QuotedGrid

open QuotedTerm QuotedFormula SourceSyntax

variable {k : ℕ} {T : RootedTree (Vertex n)}

lemma meaning_reverseCycleY_move (env : Fin k → HF (Atom b)) (F R Γ ot ht st tt : QuotedTerm k)
    (P : ParentEdges T) (e : Edge n) (he : e ∉ P.treeEdges) (h : Edge n) (s t : LocalGroup h)
    (hF : ∀ z, z ∈ elements (F.meaning (atomInput b) env) ↔ ∃ C : CycleFrame n, frameCode b C = z)
    (hR : R.meaning (atomInput b) env = distancesCode b (boxGraph n))
    (hΓ : Γ.meaning (atomInput b) env = traversalCode b P.treeEdges e (tail e) (head e))
    (ho : ot.meaning (atomInput b) env = vertexCode b oppositeVertex)
    (hh : ht.meaning (atomInput b) env = edgeCode b h)
    (hs : st.meaning (atomInput b) env = atom (.inl ⟨h,s⟩))
    (ht' : tt.meaning (atomInput b) env = atom (.inl ⟨h,t⟩)) (hn : 1 ≤ n) :
    (((traversalEdge Γ ht).neg.and (eq st tt)).or
      ((traversalEdge Γ ht).and ((baseEq F ht st tt).and (directedZ R Γ ot ht st tt)))).meaning (atomInput b) env ↔
      t = restrictGroup h (⟨0,P.flow e (-1)⟩ : BoxGroup n)*s := by
  rw [meaning_or,meaning_and,meaning_neg,meaning_and,meaning_and,
    meaning_traversalEdge env Γ ht P.treeEdges e (tail e) (head e) h hΓ hh,
    P.traverses_iff_neg_nonzero e he h,
    meaning_baseEq env F ht st tt h s t hF hh hs ht' hn,
    meaning_directedZ env R Γ ot ht st tt P.treeEdges e (tail e) (head e) oppositeVertex h s t
      hR hΓ ho hh hs ht' hn,
    P.opposite_directed_flow_iff e he h (s⁻¹*t).flow,meaning_eq,hs,ht']
  have ha : atom (Sum.inl ⟨h,s⟩ : Atom b) = atom (.inl ⟨h,t⟩) ↔ s=t := by
    simp only [atom_injective.eq_iff,Sum.inl.injEq,Sigma.mk.inj_iff,heq_eq_eq,true_and]
  rw [ha]
  change _ ↔ t = (⟨0,(P.flow e (-1)).val h⟩ : LocalGroup h)*s
  rw [local_central_iff]
  by_cases hz : (P.flow e (-1)).val h = 0
  · simp only [hz,not_false_eq_true,true_and,ne_eq,not_true_eq_false,false_and,or_false]
    constructor
    · rintro rfl
      simp
    · rintro ⟨hf,htf⟩
      have hh := (local_central_iff h s t 0).mpr ⟨hf,htf⟩
      simpa only [show (⟨0,0⟩ : LocalGroup h)=1 from rfl,one_mul] using hh.symm
  · tauto

lemma meaning_reverseCycleY (env : Fin k → HF (Atom b)) (E F R Γ ot : QuotedTerm k)
    (P : ParentEdges T) (e : Edge n) (he : e ∉ P.treeEdges)
    (hE : E.meaning (atomInput b) env = ofFinset (Finset.univ.image (edgeCode b)))
    (hF : ∀ z, z ∈ elements (F.meaning (atomInput b) env) ↔ ∃ C : CycleFrame n, frameCode b C = z)
    (hR : R.meaning (atomInput b) env = distancesCode b (boxGraph n))
    (hΓ : Γ.meaning (atomInput b) env = traversalCode b P.treeEdges e (tail e) (head e))
    (ho : ot.meaning (atomInput b) env = vertexCode b oppositeVertex) (hn : 1 ≤ n) :
    (cycleY E F R Γ ot).meaning (atomInput b) env =
      relationCode (edgeActionRelation (b := b) (⟨0,P.flow e (-1)⟩ : BoxGroup n)) := by
  rw [cycleY,meaning_relation]
  apply congrArg relationCode
  ext ⟨a,c⟩
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,meaning_existsIn,QuotedTerm.meaning_up,
    hE,exists_edgeCode,
    meaning_allList,List.mem_cons,List.mem_nil_iff,forall_eq_or_imp,forall_false,implies_true,and_true,
    meaning_mem,meaning_var,Fin.cons_zero,Fin.cons_one,fin_cons_two,mem_edgeCode_iff,
    mem_edgeActionRelation]
  constructor
  · rintro ⟨h,⟨s,hs⟩,⟨t,ht⟩,hm⟩
    have hs' := atom_injective hs
    have ht' := atom_injective ht
    subst a
    subst c
    have hmove := (meaning_reverseCycleY_move
      (Fin.cons (edgeCode b h) (Fin.cons (atom (.inl ⟨h,t⟩)) (Fin.cons (atom (.inl ⟨h,s⟩)) env)))
      F.up.up.up R.up.up.up Γ.up.up.up ot.up.up.up (var 0) (var 2) (var 1)
      P e he h s t hF hR hΓ ho rfl rfl rfl hn).mp hm
    exact ⟨h,s,rfl,congrArg (fun t : LocalGroup h => (Sum.inl ⟨h,t⟩ : Atom b)) hmove⟩
  · rintro ⟨h,s,rfl,rfl⟩
    refine ⟨h,⟨s,rfl⟩,⟨restrictGroup h (⟨0,P.flow e (-1)⟩ : BoxGroup n)*s,rfl⟩,?_⟩
    exact (meaning_reverseCycleY_move
      (Fin.cons (edgeCode b h) (Fin.cons (atom (.inl ⟨h,restrictGroup h (⟨0,P.flow e (-1)⟩ : BoxGroup n)*s⟩))
        (Fin.cons (atom (.inl ⟨h,s⟩)) env)))
      F.up.up.up R.up.up.up Γ.up.up.up ot.up.up.up (var 0) (var 2) (var 1)
      P e he h s _ hF hR hΓ ho rfl rfl rfl hn).mpr rfl

end QuotedGrid

end





noncomputable section

open Classical WitnessedChoice

variable {n : ℕ}

abbrev VertexKey := Lex (Fin 4 → ℕ)

def vertexKey (α : Fin 4 → Vertex n) := AnchoredTree.key (boxGraph n) α

def lowEnd (α : Fin 4 → Vertex n) (e : Edge n) : Vertex n :=
  if vertexKey α (tail e) < vertexKey α (head e) then tail e else head e

def highEnd (α : Fin 4 → Vertex n) (e : Edge n) : Vertex n :=
  if vertexKey α (tail e) < vertexKey α (head e) then head e else tail e

def edgeKey (α : Fin 4 → Vertex n) (e : Edge n) : Lex (VertexKey × VertexKey) :=
  toLex (vertexKey α (lowEnd α e),vertexKey α (highEnd α e))

lemma low_high_endpoints (α : Fin 4 → Vertex n) (e : Edge n) :
    (lowEnd α e = tail e ∧ highEnd α e = head e) ∨
      (highEnd α e = tail e ∧ lowEnd α e = head e) := by
  unfold lowEnd highEnd
  split_ifs <;> simp

lemma low_lt_high (α : Fin 4 → Vertex n) (hα : AnchoredTree.Resolving (boxGraph n) α) (e : Edge n) :
    vertexKey α (lowEnd α e) < vertexKey α (highEnd α e) := by
  have hne : vertexKey α (tail e) ≠ vertexKey α (head e) :=
    fun h => (head_ne_tail e) (hα h).symm
  unfold lowEnd highEnd
  split_ifs with h
  · exact h
  · exact lt_of_le_of_ne (le_of_not_gt h) hne.symm

lemma ordered_endpoints_iff (α : Fin 4 → Vertex n) (hα : AnchoredTree.Resolving (boxGraph n) α)
    (e : Edge n) (u v : Vertex n) :
    (((u=tail e ∧ v=head e) ∨ (v=tail e ∧ u=head e)) ∧ vertexKey α u < vertexKey α v) ↔
      u=lowEnd α e ∧ v=highEnd α e := by
  constructor
  · rintro ⟨(⟨rfl,rfl⟩|⟨rfl,rfl⟩),h⟩
    · simp only [lowEnd,highEnd,ite_eq_left h,and_self]
    · unfold lowEnd highEnd
      split_ifs with hh
      · exact False.elim ((not_lt_of_ge (le_of_lt h)) hh)
      · exact ⟨rfl,rfl⟩
  · rintro ⟨rfl,rfl⟩
    exact ⟨low_high_endpoints α e,low_lt_high α hα e⟩

lemma edgeKey_injective (α : Fin 4 → Vertex n) (hα : AnchoredTree.Resolving (boxGraph n) α) :
    Function.Injective (edgeKey α) := by
  intro e f h
  have h₁ := hα (congrArg (fun k : Lex (VertexKey × VertexKey) => (ofLex k).1) h)
  have h₂ := hα (congrArg (fun k : Lex (VertexKey × VertexKey) => (ofLex k).2) h)
  change lowEnd α e = lowEnd α f at h₁
  change highEnd α e = highEnd α f at h₂
  apply edge_eq_of_endpoints
  rcases low_high_endpoints α e with ⟨he,he'⟩ | ⟨he',he⟩ <;>
    rcases low_high_endpoints α f with ⟨hf,hf'⟩ | ⟨hf',hf⟩
  · exact Or.inl ⟨he.symm.trans (h₁.trans hf),he'.symm.trans (h₂.trans hf')⟩
  · exact Or.inr ⟨he.symm.trans (h₁.trans hf),he'.symm.trans (h₂.trans hf')⟩
  · exact Or.inr ⟨he'.symm.trans (h₂.trans hf'),he.symm.trans (h₁.trans hf)⟩
  · exact Or.inl ⟨he'.symm.trans (h₂.trans hf'),he.symm.trans (h₁.trans hf)⟩

def leastEdges (α : Fin 4 → Vertex n) (D : Finset (Edge n)) : Finset (Edge n) :=
  D.filter (fun e => ∀ f ∈ D, ¬edgeKey α f < edgeKey α e)

lemma leastEdges_empty_iff (α : Fin 4 → Vertex n) (D : Finset (Edge n)) :
    leastEdges α D = ∅ ↔ D=∅ := by
  constructor
  · intro h
    by_contra hn
    have hD := Finset.nonempty_iff_ne_empty.mpr hn
    let K := D.image (edgeKey α)
    have hK : K.Nonempty := hD.image _
    obtain ⟨e,he,hek⟩ := Finset.mem_image.mp (Finset.min'_mem K hK)
    have hemin : e ∈ leastEdges α D := by
      refine Finset.mem_filter.mpr ⟨he,?_⟩
      intro f hf hlt
      have hm := Finset.min'_le K (edgeKey α f) (Finset.mem_image.mpr ⟨f,hf,rfl⟩)
      rw [←hek] at hm
      exact (not_lt_of_ge hm) hlt
    rw [h] at hemin
    exact Finset.notMem_empty _ hemin
  · rintro rfl
    simp [leastEdges]

lemma leastEdges_subsingleton (α : Fin 4 → Vertex n) (hα : AnchoredTree.Resolving (boxGraph n) α)
    (D : Finset (Edge n)) : (↑(leastEdges α D) : Set (Edge n)).Subsingleton := by
  intro e he f hf
  obtain ⟨he,hm⟩ := Finset.mem_filter.mp he
  obtain ⟨hf,hn⟩ := Finset.mem_filter.mp hf
  exact edgeKey_injective α hα (le_antisymm (le_of_not_gt (hm f hf)) (le_of_not_gt (hn e he)))

end





noncomputable section

open Classical WitnessedChoice WitnessedChoice.BGS Hereditary

variable {n : ℕ} {b : Vertex n → Scalar}

namespace QuotedGrid

open QuotedTerm QuotedFormula

variable {k : ℕ}

lemma meaning_edgeLt (env : Fin k → HF (Atom b)) (ats VT R et ft : QuotedTerm k)
    (α : Fin 4 → Vertex n) (e f : Edge n) (hres : AnchoredTree.Resolving (boxGraph n) α)
    (hα : ats.meaning (atomInput b) env = tupleCode (List.ofFn (vertexCode b ∘ α)))
    (hV : VT.meaning (atomInput b) env = ofFinset (Finset.univ.image (vertexCode b)))
    (hR : R.meaning (atomInput b) env = ofFinset
      ((BFS.closure (boxGraph n) (Fintype.card (Atom b))).image (distanceCode (vertexCode b))))
    (he : et.meaning (atomInput b) env = edgeCode b e)
    (hf : ft.meaning (atomInput b) env = edgeCode b f) (hn : 1 ≤ n) :
    (edgeLt ats VT R et ft).meaning (atomInput b) env ↔ edgeKey α e < edgeKey α f := by
  have hlt {l : ℕ} (env' : Fin l → HF (Atom b)) (at' R' ut vt : QuotedTerm l) (u v : Vertex n)
      (hat : at'.meaning (atomInput b) env' = tupleCode (List.ofFn (vertexCode b ∘ α)))
      (hR' : R'.meaning (atomInput b) env' = R.meaning (atomInput b) env)
      (hu : ut.meaning (atomInput b) env' = vertexCode b u)
      (hv : vt.meaning (atomInput b) env' = vertexCode b v) :
      (vertexLt at' R' ut vt).meaning (atomInput b) env' ↔ vertexKey α u < vertexKey α v := by
    exact QuotedFormula.meaning_vertexLt (atomInput b) env' at' R' ut vt (vertexCode b)
      (vertexCode_injective hn) (boxGraph n) (boxGraph_connected n) α u v hat (hR'.trans hR) hu hv (vertex_card_le_atoms hn)
  have hm (u v w z : Vertex n) := hlt
    (Fin.cons (vertexCode b z) (Fin.cons (vertexCode b w) (Fin.cons (vertexCode b v) (Fin.cons (vertexCode b u) env))))
    ats.up.up.up.up R.up.up.up.up
  have hp (u v w z : Vertex n) := meaning_hasEndpoints
    (Fin.cons (vertexCode b z) (Fin.cons (vertexCode b w) (Fin.cons (vertexCode b v) (Fin.cons (vertexCode b u) env))))
  simp only [edgeLt,meaning_existsIn,QuotedTerm.meaning_up,hV,elements_ofFinset,Finset.mem_image,
    Finset.mem_univ,true_and,exists_exists_eq_and,meaning_allList,List.mem_cons,
    List.mem_nil_iff,forall_eq_or_imp,forall_false,implies_true,and_true,meaning_and,meaning_or,meaning_eq,
    meaning_var,Fin.cons_zero,Fin.cons_one,fin_cons_two,fin_cons_three,(vertexCode_injective hn).eq_iff]
  have hh (u v w z : Vertex n) :
      (hasEndpoints et.up.up.up.up (var 3) (var 2)).meaning (atomInput b)
        (Fin.cons (vertexCode b z) (Fin.cons (vertexCode b w) (Fin.cons (vertexCode b v) (Fin.cons (vertexCode b u) env)))) ↔
          (u=tail e ∧ v=head e) ∨ (v=tail e ∧ u=head e) := hp u v w z _ _ _ e u v he rfl rfl hn
  have hh' (u v w z : Vertex n) :
      (hasEndpoints ft.up.up.up.up (var 1) (var 0)).meaning (atomInput b)
        (Fin.cons (vertexCode b z) (Fin.cons (vertexCode b w) (Fin.cons (vertexCode b v) (Fin.cons (vertexCode b u) env)))) ↔
          (w=tail f ∧ z=head f) ∨ (z=tail f ∧ w=head f) := hp u v w z _ _ _ f w z hf rfl rfl hn
  have hm32 (u v w z : Vertex n) :
      (vertexLt ats.up.up.up.up R.up.up.up.up (var 3) (var 2)).meaning (atomInput b)
        (Fin.cons (vertexCode b z) (Fin.cons (vertexCode b w) (Fin.cons (vertexCode b v) (Fin.cons (vertexCode b u) env)))) ↔
          vertexKey α u < vertexKey α v := hm u v w z _ _ u v hα rfl rfl rfl
  have hm10 (u v w z : Vertex n) :
      (vertexLt ats.up.up.up.up R.up.up.up.up (var 1) (var 0)).meaning (atomInput b)
        (Fin.cons (vertexCode b z) (Fin.cons (vertexCode b w) (Fin.cons (vertexCode b v) (Fin.cons (vertexCode b u) env)))) ↔
          vertexKey α w < vertexKey α z := hm u v w z _ _ w z hα rfl rfl rfl
  have hm31 (u v w z : Vertex n) :
      (vertexLt ats.up.up.up.up R.up.up.up.up (var 3) (var 1)).meaning (atomInput b)
        (Fin.cons (vertexCode b z) (Fin.cons (vertexCode b w) (Fin.cons (vertexCode b v) (Fin.cons (vertexCode b u) env)))) ↔
          vertexKey α u < vertexKey α w := hm u v w z _ _ u w hα rfl rfl rfl
  have hm20 (u v w z : Vertex n) :
      (vertexLt ats.up.up.up.up R.up.up.up.up (var 2) (var 0)).meaning (atomInput b)
        (Fin.cons (vertexCode b z) (Fin.cons (vertexCode b w) (Fin.cons (vertexCode b v) (Fin.cons (vertexCode b u) env)))) ↔
          vertexKey α v < vertexKey α z := hm u v w z _ _ v z hα rfl rfl rfl
  simp only [hh,hh',hm32,hm10,hm31,hm20]
  constructor
  · rintro ⟨u,v,w,z,he,hf,huv,hwz,h⟩
    obtain ⟨rfl,rfl⟩ := (ordered_endpoints_iff α hres e u v).mp ⟨he,huv⟩
    obtain ⟨rfl,rfl⟩ := (ordered_endpoints_iff α hres f w z).mp ⟨hf,hwz⟩
    rw [edgeKey,edgeKey,Prod.Lex.toLex_lt_toLex]
    exact h.imp id (fun ⟨he,hl⟩ => ⟨congrArg (vertexKey α) he,hl⟩)
  · intro h
    rw [edgeKey,edgeKey,Prod.Lex.toLex_lt_toLex] at h
    exact ⟨lowEnd α e,highEnd α e,lowEnd α f,highEnd α f,
      low_high_endpoints α e,low_high_endpoints α f,low_lt_high α hres e,low_lt_high α hres f,
      h.imp id (fun ⟨he,hl⟩ => ⟨hres he,hl⟩)⟩

end QuotedGrid

end





noncomputable section

open Classical WitnessedChoice WitnessedChoice.BGS Hereditary

variable {n : ℕ} {b : Vertex n → Scalar}

def missingEdge (x : Finset (Σ e : Edge n, LocalGroup e)) (e : Edge n) : Prop :=
  ∀ r ∈ x, r.1 ≠ e

def remainingEdges (T : Finset (Edge n)) (x : Finset (Σ e : Edge n, LocalGroup e)) : Finset (Edge n) :=
  (Finset.univ \ T).filter (missingEdge x)

lemma selected_inter_empty (x : Finset (Σ e : Edge n, LocalGroup e)) (e : Edge n) :
    ofFinset ((elements (stateCode (x.image Sum.inl : Finset (Atom b)))) ∩ elements (edgeCode b e)) = emptyHF ↔
      missingEdge x e := by
  rw [show emptyHF = (ofFinset ∅ : HF (Atom b)) from rfl, ofFinset_inj,Finset.eq_empty_iff_forall_notMem]
  simp only [Finset.mem_inter,stateCode,elements_ofFinset,Finset.image_image,Finset.mem_image,Function.comp_apply]
  constructor
  · intro h r hr he
    exact h (atom (.inl r)) ⟨⟨r,hr,rfl⟩,(atom_mem_edgeCode _ _ _).mpr he⟩
  · rintro h z ⟨⟨r,hr,rfl⟩,he⟩
    exact h r hr ((atom_mem_edgeCode _ _ _).mp he)

namespace QuotedGrid

open QuotedTerm QuotedFormula

variable {k : ℕ}

lemma meaning_nextEdges (env : Fin k → HF (Atom b)) (ats VT ET R TT xt : QuotedTerm k)
    (α : Fin 4 → Vertex n) (T : Finset (Edge n)) (x : Finset (Σ e : Edge n, LocalGroup e))
    (hres : AnchoredTree.Resolving (boxGraph n) α)
    (hα : ats.meaning (atomInput b) env = tupleCode (List.ofFn (vertexCode b ∘ α)))
    (hV : VT.meaning (atomInput b) env = ofFinset (Finset.univ.image (vertexCode b)))
    (hE : ET.meaning (atomInput b) env = ofFinset (Finset.univ.image (edgeCode b)))
    (hR : R.meaning (atomInput b) env = ofFinset
      ((BFS.closure (boxGraph n) (Fintype.card (Atom b))).image (distanceCode (vertexCode b))))
    (hT : TT.meaning (atomInput b) env = ofFinset (T.image (edgeCode b)))
    (hx : xt.meaning (atomInput b) env = stateCode (x.image Sum.inl)) (hn : 1 ≤ n) :
    (nextEdges ats VT ET R TT xt).meaning (atomInput b) env =
      ofFinset ((leastEdges α (remainingEdges T x)).image (edgeCode b)) := by
  have hd : (ET.diff TT).meaning (atomInput b) env = ofFinset ((Finset.univ \ T).image (edgeCode b)) := by
    simp only [meaning_diff,hE,hT,elements_ofFinset]
    apply ofFinset_inj.mpr
    ext z
    simp only [Finset.mem_filter,Finset.mem_image,Finset.mem_univ,true_and,Finset.mem_sdiff,
      not_exists,not_and]
    constructor
    · rintro ⟨⟨e,rfl⟩,he⟩
      refine ⟨e,?_,rfl⟩
      exact fun ht => he e ht rfl
    · rintro ⟨e,he,rfl⟩
      exact ⟨⟨e,rfl⟩,fun f hf hfe => he ((edgeCode_injective hfe) ▸ hf)⟩
  have hmiss {l : ℕ} (env' : Fin l → HF (Atom b)) (x' e' : QuotedTerm l) (e : Edge n)
      (hx' : x'.meaning (atomInput b) env' = stateCode (x.image Sum.inl))
      (he' : e'.meaning (atomInput b) env' = edgeCode b e) :
      (eq (x'.inter e') empty).meaning (atomInput b) env' ↔ missingEdge x e := by
    simp only [meaning_eq,meaning_inter,hx',he',meaning_empty]
    exact selected_inter_empty x e
  have hm1 (e : Edge n) := hmiss (Fin.cons (edgeCode b e) env) xt.up (var 0) e hx rfl
  have hm2 (e f : Edge n) := hmiss (Fin.cons (edgeCode b f) (Fin.cons (edgeCode b e) env)) xt.up.up (var 0) f hx rfl
  have ho (e f : Edge n) := meaning_edgeLt (Fin.cons (edgeCode b f) (Fin.cons (edgeCode b e) env))
    ats.up.up VT.up.up R.up.up (var 0) (var 1) α f e hres hα hV hR rfl rfl hn
  simp only [nextEdges,QuotedTerm.meaning_filter,hd,elements_ofFinset]
  apply ofFinset_inj.mpr
  ext z
  simp only [Finset.mem_filter,Finset.mem_image]
  constructor
  · rintro ⟨⟨⟨e,he,rfl⟩,hm⟩,hmin⟩
    refine ⟨e,Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨he,(hm1 e).mp hm⟩,?_⟩,rfl⟩
    simp only [meaning_allIn,QuotedTerm.meaning_up,hd,elements_ofFinset,Finset.forall_mem_image,meaning_neg,meaning_and,hm2,ho] at hmin
    intro f hf
    obtain ⟨hf,hfm⟩ := Finset.mem_filter.mp hf
    exact fun hlt => hmin hf ⟨hfm,hlt⟩
  · rintro ⟨e,he,rfl⟩
    obtain ⟨he,hmin⟩ := Finset.mem_filter.mp he
    obtain ⟨he,hm⟩ := Finset.mem_filter.mp he
    refine ⟨⟨⟨e,he,rfl⟩,(hm1 e).mpr hm⟩,?_⟩
    simp only [meaning_allIn,QuotedTerm.meaning_up,hd,elements_ofFinset,Finset.forall_mem_image,meaning_neg,meaning_and,hm2,ho]
    intro f hf ⟨hfm,hlt⟩
    exact hmin f (Finset.mem_filter.mpr ⟨hf,hfm⟩) hlt

end QuotedGrid

end





noncomputable section

open Classical WitnessedChoice

variable {n : ℕ}

def gridCandidates (α : Fin 4 → Vertex n) (T : Finset (Edge n))
    (x : Finset (Σ e : Edge n, LocalGroup e)) : Finset (Σ e : Edge n, LocalGroup e) :=
  Finset.univ.filter fun r => r.1 ∈ leastEdges α (remainingEdges T x) ∧ AcceptsFaces x r.1 r.2

lemma mem_gridCandidates (α : Fin 4 → Vertex n) (T : Finset (Edge n))
    (x : Finset (Σ e : Edge n, LocalGroup e)) (r : Σ e : Edge n, LocalGroup e) :
    r ∈ gridCandidates α T x ↔ r.1 ∈ leastEdges α (remainingEdges T x) ∧ AcceptsFaces x r.1 r.2 := by
  simp only [gridCandidates,Finset.mem_filter,Finset.mem_univ,true_and]

lemma candidate_new_edge {α : Fin 4 → Vertex n} {T : Finset (Edge n)}
    {x : Finset (Σ e : Edge n, LocalGroup e)} {r : Σ e : Edge n, LocalGroup e}
    (hr : r ∈ gridCandidates α T x) : r.1 ∉ T ∧ missingEdge x r.1 := by
  obtain ⟨hh,_⟩ := (mem_gridCandidates α T x r).mp hr
  have he := (Finset.mem_filter.mp hh).1
  simpa only [remainingEdges,Finset.mem_filter,Finset.mem_sdiff,Finset.mem_univ,true_and] using he

lemma gridCandidates_fresh {α : Fin 4 → Vertex n} {T : Finset (Edge n)}
    {x : Finset (Σ e : Edge n, LocalGroup e)} {r : Σ e : Edge n, LocalGroup e}
    (hr : r ∈ gridCandidates α T x) : r ∉ x := fun hx => (candidate_new_edge hr).2 r hx rfl

lemma consistent_empty : ConsistentSelection (∅ : Finset (Σ e : Edge n, LocalGroup e)) := by
  simp [ConsistentSelection]

lemma consistent_insert {x : Finset (Σ e : Edge n, LocalGroup e)}
    (hx : ConsistentSelection x) {e : Edge n} {s : LocalGroup e}
    (hnew : missingEdge x e) (hs : AcceptsFaces x e s) : ConsistentSelection (insert ⟨e,s⟩ x) := by
  constructor
  · intro r hr t ht heq
    rcases Finset.mem_insert.mp hr with rfl | hr <;>
      rcases Finset.mem_insert.mp ht with rfl | ht
    · rfl
    · exact False.elim (hnew t ht heq.symm)
    · exact False.elim (hnew r hr heq)
    · exact hx.1 r hr t ht heq
  · intro r hr t ht f hf ht'
    rcases Finset.mem_insert.mp hr with rfl | hr <;>
      rcases Finset.mem_insert.mp ht with rfl | ht
    · rfl
    · exact hs t ht f hf ht'
    · exact (hs r hr f ht' hf).symm
    · exact hx.2 r hr t ht f hf ht'

lemma selectedVectors_accepts {x : Finset (Σ e : Edge n, LocalGroup e)}
    (hx : ConsistentSelection x) (e : Edge n) :
    AcceptsFaces x e (globalStates (selectedVectors x) 0 e) := by
  intro r hr f he hf
  exact selectedVectors_preserves hx hr ⟨f,hf⟩

lemma gridCandidates_empty_iff (α : Fin 4 → Vertex n) (T : Finset (Edge n))
    (x : Finset (Σ e : Edge n, LocalGroup e)) (hx : ConsistentSelection x) :
    gridCandidates α T x = ∅ ↔ remainingEdges T x = ∅ := by
  rw [←leastEdges_empty_iff α (remainingEdges T x)]
  constructor
  · intro h
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro e he
    have hm := (mem_gridCandidates α T x ⟨e,globalStates (selectedVectors x) 0 e⟩).mpr
      ⟨he,selectedVectors_accepts hx e⟩
    rw [h] at hm
    exact Finset.notMem_empty _ hm
  · intro h
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro r hr
    have hm := (mem_gridCandidates α T x r).mp hr |>.1
    rw [h] at hm
    exact Finset.notMem_empty _ hm

lemma remaining_empty_iff (T : Finset (Edge n)) (x : Finset (Σ e : Edge n, LocalGroup e)) :
    remainingEdges T x = ∅ ↔ ∀ e, e ∉ T → ∃ r ∈ x, r.1 = e := by
  simp only [Finset.eq_empty_iff_forall_notMem,remainingEdges,Finset.mem_filter,
    Finset.mem_sdiff,Finset.mem_univ,true_and,not_and,missingEdge,not_forall,not_not]
  constructor <;> intro H e he
  · obtain ⟨r,hr,hre⟩ := H e he
    exact ⟨r,hr,hre⟩
  · obtain ⟨r,hr,hre⟩ := H e he
    exact ⟨r,hr,hre⟩

end





noncomputable section

open Classical WitnessedChoice WitnessedChoice.TreeTest RelationPools

variable {n : ℕ} {b : Vertex n → Scalar}

lemma actionPerm_edgeBlock (g : BoxGroup n) (e : Edge n) :
    (edgeBlockSet b e).image (actionPerm g) = edgeBlockSet b e := by
  apply Finset.eq_of_subset_of_card_le
  · intro a ha
    obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨s,rfl⟩ := (mem_edgeBlockSet e d).mp hd
    exact (mem_edgeBlockSet e _).mpr ⟨restrictGroup e g*s,rfl⟩
  · rw [Finset.card_image_of_injective _ (actionPerm g).injective]

lemma actionPerm_vertexBlock (g : BoxGroup n) (v : Vertex n) :
    (vertexBlockSet b v).image (actionPerm g) = vertexBlockSet b v := by
  apply Finset.eq_of_subset_of_card_le
  · intro a ha
    obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨s,rfl⟩ := (mem_vertexBlockSet v d).mp hd
    exact (mem_vertexBlockSet v _).mpr ⟨actConfiguration g s,rfl⟩
  · rw [Finset.card_image_of_injective _ (actionPerm g).injective]

lemma actionPerm_blocks (hn : 1 ≤ n) (g : BoxGroup n) :
    ∀ u ∈ blocks (atomInput b), u.image (actionPerm g) = u := by
  intro u hu
  rcases Finset.mem_union.mp hu with hu | hu
  · rw [edgeBlocks_grid] at hu
    obtain ⟨e,_,rfl⟩ := Finset.mem_image.mp hu
    exact actionPerm_edgeBlock g e
  · rw [vertexBlocks_grid hn] at hu
    obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp hu
    exact actionPerm_vertexBlock g v

namespace ParentEdges

variable {T : RootedTree (Vertex n)} (P : ParentEdges T)

def fundamentalPool (N : Finset (Edge n)) : Finset (Relation (Atom b)) :=
  (N.product Finset.univ).image fun ea => graph (actionPerm (⟨0,P.flow ea.1 ea.2⟩ : BoxGroup n))

lemma fundamental_mem {N : Finset (Edge n)} {e : Edge n} (he : e ∈ N) (a : Scalar) :
    graph (actionPerm (b := b) (⟨0,P.flow e a⟩ : BoxGroup n)) ∈ P.fundamentalPool N :=
  Finset.mem_image.mpr ⟨(e,a),Finset.mem_product.mpr ⟨he,Finset.mem_univ _⟩,rfl⟩

lemma grid_transitivity (hn : 1 ≤ n) (α : Fin 4 → Vertex n)
    (hα : AnchoredTree.Resolving (boxGraph n) α)
    (x : Finset (Σ e : Edge n, LocalGroup e)) (hoff : ∀ r ∈ x, r.1 ∉ P.treeEdges)
    (r t : Σ e : Edge n, LocalGroup e)
    (hr : r ∈ gridCandidates α P.treeEdges x) (ht : t ∈ gridCandidates α P.treeEdges x) :
    ∃ g ∈ witnessPool localBound (atomInput b) True
      (fun _ => P.fundamentalPool (leastEdges α (remainingEdges P.treeEdges x))) (x.image Sum.inl),
      g (.inl r) = .inl t := by
  obtain ⟨hrN,hrs⟩ := (mem_gridCandidates α P.treeEdges x r).mp hr
  obtain ⟨htN,hts⟩ := (mem_gridCandidates α P.treeEdges x t).mp ht
  have ret := leastEdges_subsingleton α hα _ hrN htN
  rcases r with ⟨e,s⟩
  rcases t with ⟨e',t⟩
  dsimp at ret
  subst e'
  have hen := (candidate_new_edge hr).1
  have hnew := (candidate_new_edge hr).2
  let l := actionPerm (b := b) (⟨faceDelta e s t,0⟩ : BoxGroup n)
  let a := t.flow - (restrictGroup e (⟨faceDelta e s t,0⟩ : BoxGroup n) * s).flow
  let c := actionPerm (b := b) (⟨0,P.flow e a⟩ : BoxGroup n)
  have fixl : ∀ r ∈ x, l (.inl r) = .inl r := fun r hr => faceDelta_fix_past hrs hts hr
  have fixc : ∀ r ∈ x, c (.inl r) = .inl r := by
    intro r hr
    apply central_fix_edge
    exact P.flow_other e r.1 (hoff r hr) (hnew r hr) a
  have hfilter : PoolFilter (atomInput b) (x.image Sum.inl) (c*l) := by
    refine ⟨(fullAut (atomInput b)).mul_mem (actionPerm_fullAut _) (actionPerm_fullAut _),?_,?_⟩
    · intro u hu
      change u.image (c ∘ l) = u
      rw [←Finset.image_image,actionPerm_blocks hn _ u hu,actionPerm_blocks hn _ u hu]
    · intro a ha
      obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp ha
      change c (l (.inl r)) = _
      rw [fixl r hr,fixc r hr]
  refine ⟨c*l,?_,?_⟩
  · rw [witnessPool,ite_eq_left True.intro]
    apply Finset.mem_insert_of_mem
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    exact ⟨hfilter,graph l,faceDelta_in_localPool hn e s t,
      graph c,P.fundamental_mem hrN a,compose_graph l c⟩
  · exact central_after_local e s t (P.flow e a) (P.flow_self e hen a)

end ParentEdges

end





noncomputable section

open Classical WitnessedChoice WitnessedChoice.TreeTest

variable {n : ℕ} {b : Vertex n → Scalar}

def edgeState (x : Finset (Σ e : Edge n, LocalGroup e)) : Finset (Atom b) := x.image Sum.inl

@[simp] lemma edgeState_empty : edgeState (b := b) ∅ = ∅ := Finset.image_empty _

@[simp] lemma edgeState_insert (r : Σ e : Edge n, LocalGroup e) (x) :
    edgeState (b := b) (insert r x) = insert (.inl r) (edgeState x) := Finset.image_insert _ _ _

lemma edgeState_injective : Function.Injective (edgeState (b := b)) :=
  fun _ _ h => (Finset.image_inj Sum.inl_injective).mp h

lemma mem_edgeState (x : Finset (Σ e : Edge n, LocalGroup e)) (a : Atom b) :
    a ∈ edgeState x ↔ ∃ r ∈ x, Sum.inl r = a := Finset.mem_image

namespace ParentEdges

variable {T : RootedTree (Vertex n)} (P : ParentEdges T)

lemma prefix_invariant (α : Fin 4 → Vertex n) (S : Selection (Atom b))
    (hD : ∀ x, S.candidates (edgeState x) = edgeState (gridCandidates α P.treeEdges x))
    {B : ℕ → Finset (Atom b)} {c : ℕ → Option (Atom b)} {k : ℕ} (hpath : S.Prefix B c k) :
    ∀ i ≤ k, ∃ x : Finset (Σ e : Edge n, LocalGroup e),
      B i = edgeState x ∧ ConsistentSelection x ∧ ∀ r ∈ x, r.1 ∉ P.treeEdges := by
  intro i
  induction i with
  | zero =>
    intro _
    exact ⟨∅,hpath.1.trans edgeState_empty.symm,consistent_empty,by simp⟩
  | succ i ih =>
    intro hi
    obtain ⟨x,hx,hcons,hoff⟩ := ih (by omega)
    obtain ⟨hc,hstep⟩ := hpath.2 i (by omega)
    cases hci : c i with
    | none =>
      rw [hci] at hstep
      exact ⟨x,hstep.trans hx,hcons,hoff⟩
    | some a =>
      rw [hci] at hc hstep
      have ha := (Selection.some_mem_choices.mp hc).1
      rw [hx,hD] at ha
      obtain ⟨r,hr,rfl⟩ := (mem_edgeState _ a).mp ha
      obtain ⟨hne,hnew⟩ := candidate_new_edge hr
      have hh : B (i+1) = edgeState (insert r x) := by
        rw [hstep,hx,Selection.advance,edgeState_insert]
      refine ⟨insert r x,hh,consistent_insert hcons hnew ((mem_gridCandidates _ _ _ _).mp hr).2,?_⟩
      intro s hs
      rcases Finset.mem_insert.mp hs with rfl | hs
      · exact hne
      · exact hoff s hs

lemma terminal_complete (α : Fin 4 → Vertex n) (S : Selection (Atom b))
    (hD : ∀ x, S.candidates (edgeState x) = edgeState (gridCandidates α P.treeEdges x))
    (hTrans : ∀ x, ConsistentSelection x → (∀ r ∈ x, r.1 ∉ P.treeEdges) →
      S.TransitiveAt (edgeState x))
    {B : ℕ → Finset (Atom b)} {c : ℕ → Option (Atom b)} {t : ℕ} (hpath : S.FirstStabilization B c t) :
    ∃ x : Finset (Σ e : Edge n, LocalGroup e), B t = edgeState x ∧ ConsistentSelection x ∧
      (∀ r ∈ x, r.1 ∉ P.treeEdges) ∧ ∀ e, e ∉ P.treeEdges → ∃ r ∈ x, r.1 = e := by
  obtain ⟨x,hx,hcons,hoff⟩ := P.prefix_invariant α S hD hpath.1 t (by omega)
  refine ⟨x,hx,hcons,hoff,(remaining_empty_iff P.treeEdges x).mp ?_⟩
  apply (gridCandidates_empty_iff α P.treeEdges x hcons).mp
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro r hr
  have hne : (S.candidates (B t)).Nonempty := by
    rw [hx,hD]
    exact ⟨.inl r,(mem_edgeState _ _).mpr ⟨r,hr,rfl⟩⟩
  have ht : S.TransitiveAt (B t) := hx.symm ▸ hTrans x hcons hoff
  have hc := (hpath.1.2 t (by omega)).1
  have hs := (hpath.1.2 t (by omega)).2
  cases hci : c t with
  | none =>
    rw [hci] at hc
    exact (Selection.none_mem_choices.mp hc) ⟨hne,ht⟩
  | some a =>
    rw [hci] at hc hs
    have ha := (Selection.some_mem_choices.mp hc).1
    rw [hx,hD] at ha
    obtain ⟨s,hsc,rfl⟩ := (mem_edgeState _ a).mp ha
    simp only [Selection.advance] at hs
    have heq : insert s x = x := by
      apply edgeState_injective
      rw [edgeState_insert,←hx,←hs,←hpath.2.2]
    have hmem : s ∈ x := by rw [←heq]; exact Finset.mem_insert_self _ _
    exact gridCandidates_fresh hsc hmem

end ParentEdges

end





noncomputable section

open Classical WitnessedChoice WitnessedChoice.BGS WitnessedChoice.TreeTest Hereditary RelationPools

variable {n : ℕ} {b : Vertex n → Scalar}

namespace QuotedGrid

open QuotedTerm QuotedFormula SourceSyntax

variable {k : ℕ}

lemma meaning_cycleRelation_of_Y (env : Fin k → HF (Atom b)) (V E F R Γ ot : QuotedTerm k)
    (g : BoxGroup n)
    (hV : V.meaning (atomInput b) env = ofFinset (Finset.univ.image (vertexCode b)))
    (hE : E.meaning (atomInput b) env = ofFinset (Finset.univ.image (edgeCode b)))
    (hY : (cycleY E F R Γ ot).meaning (atomInput b) env = relationCode (edgeActionRelation g))
    (hn : 1 ≤ n) :
    (cycleRelation V E F R Γ ot).meaning (atomInput b) env = relationCode (graph (actionPerm g)) := by
  rw [cycleRelation,meaning_cup,hY,meaning_cycleX env V E _ g hV hE hY hn]
  simpa only [relationCode,elements_ofFinset,←Finset.image_union] using
    congrArg relationCode (edge_config_union (b := b) g)

lemma cycleRelations_mem (env : Fin k → HF (Atom b)) (V E F R T H N : QuotedTerm k)
    (Ts : Finset (Edge n)) (Ns : Finset (Edge n)) (e : Edge n) (o : Vertex n) (g : BoxGroup n)
    (hV : V.meaning (atomInput b) env = ofFinset (Finset.univ.image (vertexCode b)))
    (hE : E.meaning (atomInput b) env = ofFinset (Finset.univ.image (edgeCode b)))
    (hT : T.meaning (atomInput b) env = ofFinset (Ts.image (edgeCode b)))
    (hH : H.meaning (atomInput b) env = connTableCode b Ts)
    (hN : N.meaning (atomInput b) env = ofFinset (Ns.image (edgeCode b)))
    (he : e ∈ Ns)
    (hY : ∀ (env' : Fin (k+4) → HF (Atom b)) (Γ : QuotedTerm (k+4)),
      F.up.up.up.up.meaning (atomInput b) env' = F.meaning (atomInput b) env →
      R.up.up.up.up.meaning (atomInput b) env' = R.meaning (atomInput b) env →
      E.up.up.up.up.meaning (atomInput b) env' = E.meaning (atomInput b) env →
      Γ.meaning (atomInput b) env' = traversalCode b Ts e (tail e) (head e) →
      (var 0 : QuotedTerm (k+4)).meaning (atomInput b) env' = vertexCode b o →
      (cycleY E.up.up.up.up F.up.up.up.up R.up.up.up.up Γ (var 0)).meaning (atomInput b) env' =
        relationCode (edgeActionRelation g)) (hn : 1 ≤ n) :
    relationCode (graph (actionPerm g)) ∈ elements ((cycleRelations V E F R T H N).meaning (atomInput b) env) := by
  simp only [cycleRelations,meaning_cup,elements_ofFinset,Finset.mem_union,meaning_bind,
    QuotedTerm.meaning_up,hN,hV,Finset.mem_biUnion,Finset.mem_image,Finset.mem_univ,true_and,
    meaning_map,QuotedTerm.meaning_filter,Finset.mem_filter]
  apply Or.inr
  refine ⟨edgeCode b e,⟨e,he,rfl⟩,vertexCode b (tail e),⟨tail e,rfl⟩,
    vertexCode b (head e),⟨head e,rfl⟩,vertexCode b o,⟨⟨o,rfl⟩,?_⟩,?_⟩
  · exact (meaning_hasEndpoints _ _ _ _ e (tail e) (head e) rfl rfl rfl hn).mpr (Or.inl ⟨rfl,rfl⟩)
  · have htr := meaning_traversal
      (Fin.cons (vertexCode b o) (Fin.cons (vertexCode b (head e))
        (Fin.cons (vertexCode b (tail e)) (Fin.cons (edgeCode b e) env))))
      V.up.up.up.up T.up.up.up.up H.up.up.up.up (var 3) (var 2) (var 1)
      Ts e (tail e) (head e) hV hT hH rfl rfl rfl hn
    exact meaning_cycleRelation_of_Y _ _ _ _ _ _ _ g hV hE (hY _ _ rfl rfl rfl htr rfl) hn

end QuotedGrid

end





noncomputable section

open Classical WitnessedChoice WitnessedChoice.BGS WitnessedChoice.TreeTest Hereditary RelationPools

variable {n : ℕ} {b : Vertex n → Scalar}

namespace QuotedGrid

open QuotedTerm QuotedFormula SourceSyntax

variable {k : ℕ} {T₀ : RootedTree (Vertex n)}

attribute [local irreducible] SourceSyntax.cycleRelations SourceSyntax.cycleY

lemma cycleRelations_identity (env : Fin k → HF (Atom b)) (V E F R T H N : QuotedTerm k) :
    relationCode (graph 1) ∈ elements ((cycleRelations V E F R T H N).meaning (atomInput b) env) := by
  rw [cycleRelations,meaning_cup,elements_ofFinset]
  apply Finset.mem_union_left
  rw [meaning_singleton,Hereditary.singleton,elements_ofFinset]
  exact Finset.mem_singleton_self _

lemma cycleRelations_positive (env : Fin k → HF (Atom b)) (V E F R T H N : QuotedTerm k)
    (P : ParentEdges T₀) (Ns : Finset (Edge n))
    (hV : V.meaning (atomInput b) env = ofFinset (Finset.univ.image (vertexCode b)))
    (hE : E.meaning (atomInput b) env = ofFinset (Finset.univ.image (edgeCode b)))
    (hF : ∀ z, z ∈ elements (F.meaning (atomInput b) env) ↔ ∃ C : CycleFrame n, frameCode b C = z)
    (hR : R.meaning (atomInput b) env = distancesCode b (boxGraph n))
    (hT : T.meaning (atomInput b) env = ofFinset (P.treeEdges.image (edgeCode b)))
    (hH : H.meaning (atomInput b) env = connTableCode b P.treeEdges)
    (hN : N.meaning (atomInput b) env = ofFinset (Ns.image (edgeCode b)))
    (e : Edge n) (he : e ∈ Ns) (hne : e ∉ P.treeEdges) (hn : 1 ≤ n) :
    relationCode (graph (actionPerm (b := b) (⟨0,P.flow e 1⟩ : BoxGroup n))) ∈
      elements ((cycleRelations V E F R T H N).meaning (atomInput b) env) := by
  refine cycleRelations_mem env V E F R T H N P.treeEdges Ns e originVertex
    (⟨0,P.flow e 1⟩ : BoxGroup n) hV hE hT hH hN he ?_ hn
  intro env' Γ hF' hR' hE' hΓ ho
  have hfe : ∀ z, z ∈ elements (F.up.up.up.up.meaning (atomInput b) env') ↔
      ∃ C : CycleFrame n, frameCode b C = z := fun z => by rw [hF']; exact hF z
  exact meaning_cycleY env' E.up.up.up.up F.up.up.up.up R.up.up.up.up Γ (var 0) P e hne (hE'.trans hE) hfe (hR'.trans hR) hΓ ho hn

lemma cycleRelations_negative (env : Fin k → HF (Atom b)) (V E F R T H N : QuotedTerm k)
    (P : ParentEdges T₀) (Ns : Finset (Edge n))
    (hV : V.meaning (atomInput b) env = ofFinset (Finset.univ.image (vertexCode b)))
    (hE : E.meaning (atomInput b) env = ofFinset (Finset.univ.image (edgeCode b)))
    (hF : ∀ z, z ∈ elements (F.meaning (atomInput b) env) ↔ ∃ C : CycleFrame n, frameCode b C = z)
    (hR : R.meaning (atomInput b) env = distancesCode b (boxGraph n))
    (hT : T.meaning (atomInput b) env = ofFinset (P.treeEdges.image (edgeCode b)))
    (hH : H.meaning (atomInput b) env = connTableCode b P.treeEdges)
    (hN : N.meaning (atomInput b) env = ofFinset (Ns.image (edgeCode b)))
    (e : Edge n) (he : e ∈ Ns) (hne : e ∉ P.treeEdges) (hn : 1 ≤ n) :
    relationCode (graph (actionPerm (b := b) (⟨0,P.flow e (-1)⟩ : BoxGroup n))) ∈
      elements ((cycleRelations V E F R T H N).meaning (atomInput b) env) := by
  refine cycleRelations_mem env V E F R T H N P.treeEdges Ns e oppositeVertex
    (⟨0,P.flow e (-1)⟩ : BoxGroup n) hV hE hT hH hN he ?_ hn
  intro env' Γ hF' hR' hE' hΓ ho
  have hfe : ∀ z, z ∈ elements (F.up.up.up.up.meaning (atomInput b) env') ↔
      ∃ C : CycleFrame n, frameCode b C = z := fun z => by rw [hF']; exact hF z
  exact meaning_reverseCycleY env' E.up.up.up.up F.up.up.up.up R.up.up.up.up Γ (var 0) P e hne (hE'.trans hE) hfe (hR'.trans hR) hΓ ho hn

lemma fundamentalPool_in_cycles (env : Fin k → HF (Atom b)) (V E F R T H N : QuotedTerm k)
    (P : ParentEdges T₀) (Ns : Finset (Edge n))
    (hV : V.meaning (atomInput b) env = ofFinset (Finset.univ.image (vertexCode b)))
    (hE : E.meaning (atomInput b) env = ofFinset (Finset.univ.image (edgeCode b)))
    (hF : ∀ z, z ∈ elements (F.meaning (atomInput b) env) ↔ ∃ C : CycleFrame n, frameCode b C = z)
    (hR : R.meaning (atomInput b) env = distancesCode b (boxGraph n))
    (hT : T.meaning (atomInput b) env = ofFinset (P.treeEdges.image (edgeCode b)))
    (hH : H.meaning (atomInput b) env = connTableCode b P.treeEdges)
    (hN : N.meaning (atomInput b) env = ofFinset (Ns.image (edgeCode b)))
    (hoff : ∀ e ∈ Ns, e ∉ P.treeEdges) (hn : 1 ≤ n) :
    ∀ r ∈ P.fundamentalPool Ns,
      relationCode r ∈ elements ((cycleRelations V E F R T H N).meaning (atomInput b) env) := by
  intro r hr
  obtain ⟨⟨e,a⟩,hmem,rfl⟩ := Finset.mem_image.mp hr
  obtain ⟨he,_⟩ := Finset.mem_product.mp hmem
  rcases scalar_cases a with rfl | rfl | rfl
  · have hg : (⟨0,P.flow e 0⟩ : BoxGroup n) = 1 := by rw [P.flow_zero]; rfl
    have ha : actionPerm (b := b) (1 : BoxGroup n) = 1 := map_one (MulAction.toPermHom _ _)
    rw [hg,ha]
    exact cycleRelations_identity env V E F R T H N
  · exact cycleRelations_positive env V E F R T H N P Ns hV hE hF hR hT hH hN e he (hoff e he) hn
  · exact cycleRelations_negative env V E F R T H N P Ns hV hE hF hR hT hH hN e he (hoff e he) hn

end QuotedGrid

end





noncomputable section

open Classical WitnessedChoice WitnessedChoice.BGS Hereditary

variable {n : ℕ} {b : Vertex n → Scalar}

lemma edgeAtoms_grid : WitnessedChoice.edgeAtoms (atomInput b) =
    (Finset.univ : Finset (Σ e : Edge n, LocalGroup e)).image Sum.inl := by
  ext a
  simp only [WitnessedChoice.edgeAtoms,Finset.mem_filter,Finset.mem_univ,true_and,
    atomInput,decide_eq_true_eq,Finset.mem_image]
  constructor
  · intro h
    cases h with | ed e c => exact ⟨⟨e,c⟩,rfl⟩
  · rintro ⟨⟨e,c⟩,rfl⟩
    exact .ed e c

namespace QuotedGrid

open QuotedTerm QuotedFormula SourceSyntax SourceProgram

attribute [local irreducible] QuotedTerm.nextEdges QuotedTerm.tree SourceSyntax.candidates

lemma mem_value_candidates (p : Polynomial ℝ) (hp : GridResources p b)
    (α : Fin 4 → Vertex n) (hα : AnchoredTree.Resolving (boxGraph n) α)
    (x : Finset (Σ e : Edge n, LocalGroup e)) (hn : 1 ≤ n) (z : HF (Atom b)) :
    z ∈ elements (SourceProgram.candidates.value (atomInput b) p
      (Fin.cons (stateCode (edgeState x)) (Fin.cons (tupleCode (List.ofFn (vertexCode b ∘ α))) Fin.elim0))) ↔
      ∃ r ∈ gridCandidates α (anchoredParents α).treeEdges x, atom (.inl r) = z := by
  let env : Fin 3 → HF (Atom b) := Fin.cons (distancesCode b (boxGraph n))
    (Fin.cons (stateCode (edgeState x)) (Fin.cons (tupleCode (List.ofFn (vertexCode b ∘ α))) Fin.elim0))
  have hV := quoted_vertexBlocks (b := b) hn env
  have hE := quoted_edgeBlocks (b := b) env
  have hT := meaning_tree env (var 2) QuotedTerm.vertexBlocks QuotedTerm.edgeBlocks (var 0)
    α hα rfl hV hE rfl hn
  have hN := meaning_nextEdges env (var 2) QuotedTerm.vertexBlocks QuotedTerm.edgeBlocks (var 0)
    (tree (var 2) QuotedTerm.vertexBlocks QuotedTerm.edgeBlocks (var 0)) (var 1)
    α (anchoredParents α).treeEdges x hα rfl hV hE rfl hT rfl hn
  rw [SourceProgram.candidates,CPTTerm.value_letIn,value_distances _ p hp hn,CPTTerm.value_quoted]
  rw [mem_candidates env _ _ _ _ x (mem_faces env _ _ hV hE hn) hN rfl hn z]
  constructor
  · rintro ⟨e,he,s,hz,hs⟩
    exact ⟨⟨e,s⟩,(mem_gridCandidates _ _ _ _).mpr ⟨he,hs⟩,hz.symm⟩
  · rintro ⟨⟨e,s⟩,hr,hz⟩
    obtain ⟨he,hs⟩ := (mem_gridCandidates _ _ _ _).mp hr
    exact ⟨e,he,s,hz.symm,hs⟩

lemma selection_candidates (p : Polynomial ℝ) (hp : GridResources p b)
    (α : Fin 4 → Vertex n) (hα : AnchoredTree.Resolving (boxGraph n) α)
    (x : Finset (Σ e : Edge n, LocalGroup e)) (hn : 1 ≤ n) :
    (SourceProgram.program.body.selection (atomInput b) p
      (tupleCode (List.ofFn (vertexCode b ∘ α)))).candidates (edgeState x) =
      edgeState (gridCandidates α (anchoredParents α).treeEdges x) := by
  rw [GuardedProgram.candidates_eq]
  unfold GuardedProgram.candidateSet
  change decodeState (SourceProgram.candidates.value (atomInput b) p _) ∩
    WitnessedChoice.edgeAtoms (atomInput b) = _
  ext a
  simp only [Finset.mem_inter,decodeState,Finset.mem_filter,Finset.mem_univ,true_and,
    mem_value_candidates p hp α hα x hn,atom_injective.eq_iff,mem_edgeState]
  constructor
  · exact fun h => h.1
  · rintro ⟨r,hr,rfl⟩
    refine ⟨⟨r,hr,rfl⟩,?_⟩
    rw [edgeAtoms_grid]
    exact Finset.mem_image.mpr ⟨r,Finset.mem_univ _,rfl⟩

end QuotedGrid

end

end WitnessedSeparation.Grid

end OAI
