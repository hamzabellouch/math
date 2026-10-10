import OAI.Combinatorics.ParityLifts.Evaluation

namespace OAI

namespace ParityWL.Complexity

def ClauseList.map {α β : Type} (f : α → β) (F : ClauseList α) : ClauseList β :=
  List.map (List.map f) F

lemma ClauseList.map_encode {α β : Type} [TreeCodec α] [TreeCodec β]
    (f : α → β) (hf : ∀ a, treeEncode (f a)=treeEncode a) (F : ClauseList α) :
    treeEncode (ClauseList.map f F)=treeEncode F :=
  treeEncode_map (List.map f) (treeEncode_map f hf) F

lemma minimizeList_map_encode {α β : Type} [TreeCodec α] [TreeCodec β]
    [DecidableEq α] [DecidableEq β] (f : α → β)
    (hf : ∀ a, treeEncode (f a)=treeEncode a) (F : ClauseList α) :
    minimizeList (ClauseList.map f F)=ClauseList.map f (minimizeList F) := by
  apply TreeCodec.injective
  change treeEncode (minimizeList (ClauseList.map f F))=treeEncode (ClauseList.map f (minimizeList F))
  rw [ClauseList.map_encode f hf]
  exact ((PolyProgram.minimizeList α).encoding_natural (PolyProgram.minimizeList β)
    (PolyProgram.minimizeList_code_eq α β) F (ClauseList.map f F)
      (ClauseList.map_encode f hf F).symm).symm

lemma sparseStep_map_encode {α β : Type} [TreeCodec α] [TreeCodec β]
    [DecidableEq α] [DecidableEq β] (f : α → β)
    (hf : ∀ a, treeEncode (f a)=treeEncode a) (r : ℕ) (F : ClauseList α) :
    sparseStep r (ClauseList.map f F)=((sparseStep r F).1,
      ClauseList.map f (sparseStep r F).2.1,ClauseList.map f (sparseStep r F).2.2) := by
  apply TreeCodec.injective
  change treeEncode (sparseStep r (ClauseList.map f F))=treeEncode ((sparseStep r F).1,
      ClauseList.map f (sparseStep r F).2.1,ClauseList.map f (sparseStep r F).2.2)
  simp only [treeEncode_pair,ClauseList.map_encode f hf]
  exact ((PolyProgram.sparseStep α r).encoding_natural (PolyProgram.sparseStep β r)
    (PolyProgram.sparseStep_code_eq α β r) F (ClauseList.map f F)
      (ClauseList.map_encode f hf F).symm).symm

def SparseTree.map {α β : Type} (f : α → β) : SparseTree α → SparseTree β
  | .leaf F => .leaf (ClauseList.map f F)
  | .branch F l t => .branch (ClauseList.map f F) (l.map f) (t.map f)

@[simp] lemma SparseTree.map_root {α β : Type} (f : α → β) (T : SparseTree α) :
    (T.map f).root=ClauseList.map f T.root := by cases T <;> rfl

@[simp] lemma SparseTree.map_leaves {α β : Type} (f : α → β) (T : SparseTree α) :
    (T.map f).leaves=T.leaves.map (ClauseList.map f) := by
  induction T with
  | leaf F => rfl
  | branch F l t hl ht => simp only [map,leaves,hl,ht,List.map_append]

@[simp] lemma SparseTree.map_nodes {α β : Type} (f : α → β) (T : SparseTree α) :
    (T.map f).nodes=T.nodes := by
  induction T with
  | leaf F => rfl
  | branch F l t hl ht => simp only [map,nodes,hl,ht]

lemma SparseTree.map_valid {α β : Type} [TreeCodec α] [TreeCodec β] [DecidableEq α] [DecidableEq β]
    (f : α → β) (hf : ∀ a, treeEncode (f a)=treeEncode a) (r : ℕ) (T : SparseTree α)
    (hT : T.Valid r) : (T.map f).Valid r := by
  induction T with
  | leaf F => simpa only [map,Valid,sparseStep_map_encode f hf] using hT
  | branch F l t hl ht =>
    obtain ⟨hF,hlr,htr,hlv,htv⟩ := hT
    simpa only [map,Valid,sparseStep_map_encode f hf,map_root,hlr,htr] using
      (show (sparseStep r F).1=false ∧ ClauseList.map f l.root=ClauseList.map f l.root ∧
        ClauseList.map f t.root=ClauseList.map f t.root ∧ (l.map f).Valid r ∧ (t.map f).Valid r
        from ⟨hF,rfl,rfl,hl hlv,ht htv⟩)

lemma SparseTree.map_all {α β : Type} (f : α → β) (P : ClauseList α → Prop)
    (Q : ClauseList β → Prop) (hf : ∀ F, P F → Q (ClauseList.map f F))
    (T : SparseTree α) (hT : T.All P) : (T.map f).All Q := by
  induction T with
  | leaf F => exact hf F hT
  | branch F l t hl ht => exact ⟨hf F hT.1,hl hT.2.1,ht hT.2.2⟩

end ParityWL.Complexity

end OAI
