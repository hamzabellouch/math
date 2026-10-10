import OAI.Combinatorics.ParityLifts.LeafMachine

namespace OAI

namespace ParityWL.Complexity

noncomputable def dedupBy {α β : Type} [DecidableEq β] (f : α → β) (xs : List α) : List α :=
  xs.foldl (fun acc a => if f a∈acc.map f then acc else a::acc) []

lemma fold_dedupBy_set {α β : Type} [DecidableEq β] (f : α → β) (xs acc : List α) :
    ((xs.foldl (fun s a => if f a∈s.map f then s else a::s) acc).map f).toFinset =
      (xs.map f).toFinset ∪ (acc.map f).toFinset := by
  induction xs generalizing acc with
  | nil => simp
  | cons a xs ih =>
    rw [List.foldl_cons,ih]
    by_cases h : f a∈acc.map f
    · simp [h,Finset.insert_union,Finset.insert_eq_of_mem (Finset.mem_union_right _ (List.mem_toFinset.mpr h))]
    · simp [h,Finset.union_insert,Finset.insert_union]

lemma fold_dedupBy_nodup {α β : Type} [DecidableEq β] (f : α → β) (xs acc : List α)
    (ha : (acc.map f).Nodup) :
    ((xs.foldl (fun s a => if f a∈s.map f then s else a::s) acc).map f).Nodup := by
  induction xs generalizing acc with
  | nil => exact ha
  | cons a xs ih =>
    rw [List.foldl_cons]
    apply ih
    split
    · exact ha
    · rename_i h
      simpa using (show ¬f a∈acc.map f ∧ (acc.map f).Nodup from ⟨h,ha⟩)

@[simp] lemma dedupBy_set {α β : Type} [DecidableEq β] (f : α → β) (xs : List α) :
    ((dedupBy f xs).map f).toFinset = (xs.map f).toFinset := by
  rw [dedupBy,fold_dedupBy_set]
  simp only [List.map_nil,List.toFinset_nil,Finset.union_empty]

lemma dedupBy_nodup {α β : Type} [DecidableEq β] (f : α → β) (xs : List α) :
    ((dedupBy f xs).map f).Nodup := fold_dedupBy_nodup f xs [] (by simp)

lemma fold_dedupBy_subset {α β : Type} [DecidableEq β] (f : α → β) (xs acc : List α) :
    xs.foldl (fun s a => if f a∈s.map f then s else a::s) acc ⊆ xs++acc := by
  induction xs generalizing acc with
  | nil => simp
  | cons a xs ih =>
    rw [List.foldl_cons]
    apply List.Subset.trans (ih _)
    intro b hb
    split at hb <;> simp only [List.mem_append,List.mem_cons] at * <;> tauto

lemma dedupBy_subset {α β : Type} [DecidableEq β] (f : α → β) (xs : List α) :
    dedupBy f xs ⊆ xs := by simpa [dedupBy] using fold_dedupBy_subset f xs []

noncomputable def PolyProgram.dedupBy {α β : Type} [TreeCodec α] [DecidableEq β]
    (f : α → β) (P : PolyProgram (α × α) Bool (fun x => decide (f x.1=f x.2))) :
    PolyProgram (List α) (List α) (Complexity.dedupBy f) := by
  let sw : PolyProgram (α × List α) (List α × α) (fun x => (x.2,x.1)) :=
    .expr (.pair TExpr.input.right TExpr.input.left) (by intro x; rfl)
  let test := sw.comp (P.mapWith.comp (PolyProgram.id Bool).any)
  let test' : PolyProgram (α × List α) Bool (fun x => decide (f x.1∈x.2.map f)) := test.congr (by
    intro x
    apply Bool.eq_iff_iff.mpr
    simp only [Function.comp_def,id_eq,List.any_map,List.any_eq_true,decide_eq_true_eq,List.mem_map]
    )
  let Q := test'.ite (PolyProgram.snd α (List α)) (PolyProgram.cons α)
  have hg (a : α) (acc : List α) :
      (treeEncode (if decide (f a∈acc.map f) then acc else a::acc)).size ≤
        (treeEncode acc).size+1*((treeEncode a).size+1)^1 := by
    split <;> simp [DataTree.size]
    all_goals omega
  let F := Q.foldlGrowing 1 1 hg
  exact (((PolyProgram.id (List α)).pair (PolyProgram.const ([]:List α))).comp F).congr
    (by intro xs; simp only [decide_eq_true_eq]; rfl)

abbrev ClauseList (α : Type) := List (List α)

def listCNF {α : Type} [DecidableEq α] (F : ClauseList α) : Sparsification.CNF α :=
  (F.map List.toFinset).toFinset

@[simp] lemma mem_listCNF {α : Type} [DecidableEq α] {F : ClauseList α} {C : Finset α} :
    C∈listCNF F ↔ ∃ D∈F, D.toFinset=C := by simp [listCNF]

lemma listCNF_holds {α : Type} [DecidableEq α] (F : ClauseList α) (v : α → Prop) :
    Sparsification.Holds (listCNF F) v ↔ ∀ C∈F, ∃ a∈C, v a := by
  simp only [Sparsification.Holds,mem_listCNF,forall_exists_index,and_imp]
  constructor
  · intro h C hC; simpa using h C.toFinset C hC rfl
  · intro h C D hD he; rw [← he]; simpa using h D hD

noncomputable def compactCNF {α : Type} [DecidableEq α] (F : ClauseList α) : ClauseList α :=
  dedupBy List.toFinset F

@[simp] lemma listCNF_compact {α : Type} [DecidableEq α] (F : ClauseList α) :
    listCNF (compactCNF F) = listCNF F := by simp [listCNF,compactCNF]

lemma compactCNF_length {α : Type} [DecidableEq α] (F : ClauseList α) :
    (compactCNF F).length=(listCNF F).card := by
  have h := List.toFinset_card_of_nodup (dedupBy_nodup List.toFinset F)
  simpa only [List.length_map,dedupBy_set,compactCNF,listCNF] using h.symm

noncomputable def PolyProgram.clauseEqual (α : Type) [TreeCodec α] [DecidableEq α] :
    PolyProgram (List α × List α) Bool (fun x => decide (x.1.toFinset=x.2.toFinset)) := by
  let sw : PolyProgram (List α × List α) (List α × List α) (fun x => (x.2,x.1)) :=
    .expr (.pair TExpr.input.right TExpr.input.left) (by intro x; rfl)
  refine (((PolyProgram.subset α).pair (sw.comp (PolyProgram.subset α))).comp PolyProgram.and).congr ?_
  intro x
  apply Bool.eq_iff_iff.mpr
  simp only [Function.comp_def,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨fun h => Finset.Subset.antisymm (by simpa only [Finset.subset_iff,List.mem_toFinset] using h.1) (by simpa only [Finset.subset_iff,List.mem_toFinset] using h.2),
    fun h => ⟨by simpa only [Finset.subset_iff,List.mem_toFinset] using h.subset,by simpa only [Finset.subset_iff,List.mem_toFinset] using h.symm.subset⟩⟩

noncomputable def PolyProgram.compactCNF (α : Type) [TreeCodec α] [DecidableEq α] :
    PolyProgram (ClauseList α) (ClauseList α) Complexity.compactCNF :=
  PolyProgram.dedupBy List.toFinset (PolyProgram.clauseEqual α)

noncomputable def minimizeList {α : Type} [DecidableEq α] (F : ClauseList α) : ClauseList α :=
  (compactCNF F).filter (fun C => F.all (fun D =>
    !decide (D.toFinset⊆C.toFinset) || decide (C.toFinset⊆D.toFinset)))

lemma listCNF_minimize {α : Type} [DecidableEq α] (F : ClauseList α) :
    listCNF (minimizeList F)=Sparsification.minimize (listCNF F) := by
  ext C
  simp only [mem_listCNF,Sparsification.minimize,Finset.mem_filter,List.mem_filter,minimizeList,
    List.all_eq_true,Bool.or_eq_true,Bool.not_eq_true',decide_eq_false_iff_not,decide_eq_true_eq]
  constructor
  · rintro ⟨D,⟨hD,h⟩,rfl⟩
    have hm : D.toFinset∈listCNF F := by rw [← listCNF_compact F]; exact mem_listCNF.mpr ⟨D,hD,rfl⟩
    refine ⟨mem_listCNF.mp hm,?_⟩
    rintro E ⟨A,hA,rfl⟩ hAD
    exact (h A hA).resolve_left (not_not.mpr hAD)
  · rintro ⟨hC,h⟩
    have hc : C∈listCNF (compactCNF F) := by rw [listCNF_compact]; exact mem_listCNF.mpr hC
    obtain ⟨D,hD,rfl⟩ := mem_listCNF.mp hc
    refine ⟨D,⟨hD,?_⟩,rfl⟩
    intro A hA
    exact or_iff_not_imp_left.mpr (fun hAD => h A.toFinset ⟨A,hA,rfl⟩ (not_not.mp hAD))

noncomputable def pruneList {α : Type} [DecidableEq α] (F A : ClauseList α) : ClauseList α :=
  compactCNF (F.filter (fun C => !(A.any (fun D => decide (D.toFinset⊆C.toFinset)))) ++ A)

lemma listCNF_prune {α : Type} [DecidableEq α] (F A : ClauseList α) :
    listCNF (pruneList F A)=Sparsification.prune (listCNF F) (listCNF A) := by
  rw [pruneList,listCNF_compact]
  have ha (C : List α) : (!(A.any (fun D => decide (D.toFinset⊆C.toFinset))))=true ↔
      ¬∃ D∈A, D.toFinset⊆C.toFinset := by
    rw [Bool.not_eq_true',Bool.eq_false_iff]
    simp only [ne_eq,List.any_eq_true,decide_eq_true_eq]
  ext C
  simp only [mem_listCNF,Sparsification.prune,Finset.mem_union,Finset.mem_filter,List.mem_append,
    List.mem_filter,ha]
  constructor
  · rintro ⟨D,hD,rfl⟩
    rcases hD with ⟨hD,he⟩ | hD
    · left
      refine ⟨⟨D,hD,rfl⟩,?_⟩
      rintro ⟨E,⟨B,hB,rfl⟩,hBD⟩
      exact he ⟨B,hB,hBD⟩
    · exact Or.inr ⟨D,hD,rfl⟩
  · rintro (⟨⟨D,hD,rfl⟩,he⟩ | ⟨D,hD,rfl⟩)
    · refine ⟨D,Or.inl ⟨hD,?_⟩,rfl⟩
      rintro ⟨B,hB,hBD⟩
      exact he ⟨B.toFinset,⟨B,hB,rfl⟩,hBD⟩
    · exact ⟨D,Or.inr hD,rfl⟩

end ParityWL.Complexity

end OAI
