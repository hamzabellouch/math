import OAI.Combinatorics.ParityLifts.SparseMachine

namespace OAI

namespace ParityWL.Complexity

lemma PolyProgram.congr_code {α β : Type} [TreeCodec α] [TreeCodec β]
    {f g : α → β} (P : PolyProgram α β f) (h : ∀ x, f x = g x) :
    (P.congr h).program.code = P.program.code := by
  have he : f=g := funext h
  subst g
  rfl

lemma PolyProgram.comp_code {α β γ : Type} [TreeCodec α] [TreeCodec β] [TreeCodec γ]
    {f : α → β} {g : β → γ} (P : PolyProgram α β f) (Q : PolyProgram β γ g) :
    (P.comp Q).program.code = .seq P.program.code Q.program.code := rfl

lemma PolyProgram.pair_code {α β γ : Type} [TreeCodec α] [TreeCodec β] [TreeCodec γ]
    {f : α → β} {g : α → γ} (P : PolyProgram α β f) (Q : PolyProgram α γ g) :
    (P.pair Q).program.code = .pair P.program.code Q.program.code := rfl

lemma PolyProgram.ite_code {α β : Type} [TreeCodec α] [TreeCodec β]
    {p : α → Bool} {f g : α → β} (P : PolyProgram α Bool p)
    (F : PolyProgram α β f) (G : PolyProgram α β g) :
    (P.ite F G).program.code = .cond P.program.code G.program.code F.program.code := rfl

lemma PolyProgram.map_code_eq {α β γ δ : Type} [TreeCodec α] [TreeCodec β] [TreeCodec γ] [TreeCodec δ]
    {f : α → β} {g : γ → δ} (P : PolyProgram α β f) (Q : PolyProgram γ δ g)
    (h : P.program.code=Q.program.code) : P.map.program.code=Q.map.program.code := by
  simp only [PolyProgram.map,PolyProgram.reverse,PolyProgram.congr_code,PolyProgram.comp_code,
    PolyProgram.pair_code,PolyProgram.foldlGrowing,TreeProgram.foldl,PolyProgram.fst,PolyProgram.snd,
    PolyProgram.const,PolyProgram.id,PolyProgram.cons,PolyProgram.expr,PolyProgram.of_linear,
    TreeProgram.fst,TreeProgram.snd,TreeProgram.const,TreeProgram.id,treeEncode_nil,h]

lemma PolyProgram.mapWith_code_eq {α β γ δ ε ζ : Type} [TreeCodec α] [TreeCodec β] [TreeCodec γ]
    [TreeCodec δ] [TreeCodec ε] [TreeCodec ζ] {f : α × γ → β} {g : δ × ζ → ε}
    (P : PolyProgram (α × γ) β f) (Q : PolyProgram (δ × ζ) ε g)
    (h : P.program.code=Q.program.code) : P.mapWith.program.code=Q.mapWith.program.code := by
  simp only [PolyProgram.mapWith,PolyProgram.reverse,PolyProgram.congr_code,PolyProgram.comp_code,
    PolyProgram.pair_code,PolyProgram.foldlBounded,PolyProgram.foldlGrowing,TreeProgram.foldl,
    PolyProgram.fst,PolyProgram.snd,PolyProgram.const,PolyProgram.id,PolyProgram.cons,PolyProgram.expr,
    PolyProgram.of_linear,TreeProgram.fst,TreeProgram.snd,TreeProgram.const,TreeProgram.id,treeEncode_nil,h]

lemma PolyProgram.any_code_eq {α β : Type} [TreeCodec α] [TreeCodec β]
    {f : α → Bool} {g : β → Bool} (P : PolyProgram α Bool f) (Q : PolyProgram β Bool g)
    (h : P.program.code=Q.program.code) : P.any.program.code=Q.any.program.code := by
  simp only [PolyProgram.any,PolyProgram.congr_code,PolyProgram.comp_code,PolyProgram.pair_code,
    PolyProgram.foldlBounded,TreeProgram.foldl,PolyProgram.fst,PolyProgram.snd,PolyProgram.const,
    PolyProgram.id,PolyProgram.of_linear,TreeProgram.fst,TreeProgram.snd,TreeProgram.const,TreeProgram.id,h]

lemma PolyProgram.all_code_eq {α β : Type} [TreeCodec α] [TreeCodec β]
    {f : α → Bool} {g : β → Bool} (P : PolyProgram α Bool f) (Q : PolyProgram β Bool g)
    (h : P.program.code=Q.program.code) : P.all.program.code=Q.all.program.code := by
  simp only [PolyProgram.all,PolyProgram.congr_code,PolyProgram.comp_code]
  apply congrArg₂ FCode.seq
  · apply PolyProgram.any_code_eq
    simp only [PolyProgram.comp_code,h]
  · rfl


lemma PolyProgram.filter_code_eq {α β : Type} [TreeCodec α] [TreeCodec β]
    {f : α → Bool} {g : β → Bool} (P : PolyProgram α Bool f) (Q : PolyProgram β Bool g)
    (h : P.program.code=Q.program.code) : P.filter.program.code=Q.filter.program.code := by
  simp only [PolyProgram.filter,PolyProgram.reverse,PolyProgram.congr_code,PolyProgram.comp_code,
    PolyProgram.pair_code,PolyProgram.ite_code,PolyProgram.foldlGrowing,TreeProgram.foldl,
    PolyProgram.fst,PolyProgram.snd,PolyProgram.const,PolyProgram.id,PolyProgram.cons,PolyProgram.expr,
    PolyProgram.of_linear,TreeProgram.fst,TreeProgram.snd,TreeProgram.const,TreeProgram.id,treeEncode_nil,h]

lemma FCode.cond_congr {a b c d e f : FCode} (h₁ : a=d) (h₂ : b=e) (h₃ : c=f) :
    FCode.cond a b c=FCode.cond d e f := by rw [h₁,h₂,h₃]

macro "code_congr" : tactic => `(tactic|
  repeat' first
  | apply congrArg₂ FCode.seq
  | apply congrArg₂ FCode.pair
  | apply FCode.cond_congr
  | apply PolyProgram.mapWith_code_eq
  | apply PolyProgram.map_code_eq
  | apply PolyProgram.filter_code_eq
  | apply PolyProgram.any_code_eq
  | apply PolyProgram.all_code_eq
  | assumption
  | rfl)

lemma PolyProgram.filterWith_code_eq {α β γ δ : Type} [TreeCodec α] [TreeCodec β]
    [TreeCodec γ] [TreeCodec δ] {f : α × β → Bool} {g : γ × δ → Bool}
    (P : PolyProgram (α × β) Bool f) (Q : PolyProgram (γ × δ) Bool g)
    (h : P.program.code=Q.program.code) : P.filterWith.program.code=Q.filterWith.program.code := by
  simp only [PolyProgram.filterWith,PolyProgram.congr_code,PolyProgram.comp_code]
  apply congrArg₂ FCode.seq
  · apply congrArg₂ FCode.seq
    · apply PolyProgram.mapWith_code_eq
      simp only [PolyProgram.pair_code,h]
      rfl
    · apply PolyProgram.filter_code_eq
      rfl
  · apply PolyProgram.map_code_eq
    rfl

lemma PolyProgram.dedupBy_code_eq {α β γ δ : Type} [TreeCodec α] [TreeCodec γ]
    [DecidableEq β] [DecidableEq δ] (f : α → β) (g : γ → δ)
    (P : PolyProgram (α × α) Bool (fun x => decide (f x.1=f x.2)))
    (Q : PolyProgram (γ × γ) Bool (fun x => decide (g x.1=g x.2)))
    (h : P.program.code=Q.program.code) :
    (PolyProgram.dedupBy f P).program.code=(PolyProgram.dedupBy g Q).program.code := by
  simp only [PolyProgram.dedupBy,PolyProgram.congr_code,PolyProgram.comp_code,PolyProgram.pair_code,
    PolyProgram.ite_code,PolyProgram.foldlGrowing,TreeProgram.foldl]
  apply congrArg₂ FCode.seq
  · rfl
  · apply congrArg₂ FCode.seq
    · congr 2
      apply FCode.cond_congr
      · apply congrArg₂ FCode.seq
        · rfl
        · apply congrArg₂ FCode.seq
          · exact PolyProgram.mapWith_code_eq P Q h
          · rfl
      · rfl
      · rfl
    · rfl

lemma PolyProgram.mem_code_eq (α β : Type) [TreeCodec α] [TreeCodec β]
    [DecidableEq α] [DecidableEq β] :
    (PolyProgram.mem α).program.code=(PolyProgram.mem β).program.code := by
  simp only [PolyProgram.mem,PolyProgram.congr_code,PolyProgram.comp_code]
  code_congr

lemma PolyProgram.subset_code_eq (α β : Type) [TreeCodec α] [TreeCodec β]
    [DecidableEq α] [DecidableEq β] :
    (PolyProgram.subset α).program.code=(PolyProgram.subset β).program.code := by
  simp only [PolyProgram.subset,PolyProgram.congr_code,PolyProgram.comp_code]
  apply congrArg₂ FCode.seq
  · apply PolyProgram.mapWith_code_eq
    exact PolyProgram.mem_code_eq α β
  · rfl

lemma PolyProgram.reverse_code_eq (α β : Type) [TreeCodec α] [TreeCodec β] :
    (PolyProgram.reverse α).program.code=(PolyProgram.reverse β).program.code := by
  simp only [PolyProgram.reverse,PolyProgram.congr_code,PolyProgram.comp_code,PolyProgram.pair_code,
    PolyProgram.foldlGrowing,TreeProgram.foldl,PolyProgram.cons,PolyProgram.expr,PolyProgram.of_linear,
    PolyProgram.id,PolyProgram.const,TreeProgram.id,TreeProgram.const,treeEncode_nil]

lemma PolyProgram.append_code_eq (α β : Type) [TreeCodec α] [TreeCodec β] :
    (PolyProgram.append α).program.code=(PolyProgram.append β).program.code := by
  simp only [PolyProgram.append,PolyProgram.congr_code,PolyProgram.comp_code,PolyProgram.pair_code,
    PolyProgram.foldlGrowing,TreeProgram.foldl,PolyProgram.cons,PolyProgram.expr,PolyProgram.of_linear]
  rw [PolyProgram.reverse_code_eq α β]
  rfl

lemma PolyProgram.flatten_code_eq (α β : Type) [TreeCodec α] [TreeCodec β] :
    (PolyProgram.flatten α).program.code=(PolyProgram.flatten β).program.code := by
  simp only [PolyProgram.flatten,PolyProgram.congr_code,PolyProgram.comp_code,PolyProgram.pair_code,
    PolyProgram.foldlGrowing,TreeProgram.foldl]
  rw [PolyProgram.reverse_code_eq (List α) (List β),PolyProgram.append_code_eq α β]
  rfl

lemma PolyProgram.length_code_eq (α β : Type) [TreeCodec α] [TreeCodec β] :
    (PolyProgram.length α).program.code=(PolyProgram.length β).program.code := by
  simp only [PolyProgram.length,PolyProgram.congr_code,PolyProgram.comp_code,PolyProgram.pair_code,
    PolyProgram.foldlGrowing,TreeProgram.foldl]
  rfl

lemma PolyProgram.clauseEqual_code_eq (α β : Type) [TreeCodec α] [TreeCodec β]
    [DecidableEq α] [DecidableEq β] :
    (PolyProgram.clauseEqual α).program.code=(PolyProgram.clauseEqual β).program.code := by
  simp only [PolyProgram.clauseEqual,PolyProgram.congr_code,PolyProgram.comp_code,PolyProgram.pair_code]
  repeat' first
  | apply congrArg₂ FCode.seq
  | apply congrArg₂ FCode.pair
  | apply PolyProgram.subset_code_eq
  | rfl

lemma PolyProgram.compactCNF_code_eq (α β : Type) [TreeCodec α] [TreeCodec β]
    [DecidableEq α] [DecidableEq β] :
    (PolyProgram.compactCNF α).program.code=(PolyProgram.compactCNF β).program.code := by
  exact PolyProgram.dedupBy_code_eq _ _ _ _ (PolyProgram.clauseEqual_code_eq α β)

lemma PolyProgram.clauseSubset_code_eq (α β : Type) [TreeCodec α] [TreeCodec β]
    [DecidableEq α] [DecidableEq β] :
    (PolyProgram.clauseSubset α).program.code=(PolyProgram.clauseSubset β).program.code := by
  simp only [PolyProgram.clauseSubset,PolyProgram.congr_code]
  exact PolyProgram.subset_code_eq α β

macro "set_code_congr" : tactic => `(tactic|
  repeat' first
  | apply congrArg₂ FCode.seq | apply congrArg₂ FCode.pair | apply FCode.cond_congr
  | apply PolyProgram.mapWith_code_eq | apply PolyProgram.map_code_eq
  | apply PolyProgram.filterWith_code_eq | apply PolyProgram.filter_code_eq
  | apply PolyProgram.any_code_eq | apply PolyProgram.all_code_eq
  | apply PolyProgram.compactCNF_code_eq | apply PolyProgram.clauseSubset_code_eq
  | apply PolyProgram.clauseEqual_code_eq | apply PolyProgram.mem_code_eq
  | apply PolyProgram.append_code_eq | apply PolyProgram.flatten_code_eq | apply PolyProgram.length_code_eq | rfl)

lemma PolyProgram.minimalClause_code_eq (α β : Type) [TreeCodec α] [TreeCodec β]
    [DecidableEq α] [DecidableEq β] :
    (PolyProgram.minimalClause α).program.code=(PolyProgram.minimalClause β).program.code := by
  unfold PolyProgram.minimalClause
  simp only [PolyProgram.congr_code,PolyProgram.comp_code]
  apply congrArg₂ FCode.seq
  · rfl
  · apply congrArg₂ FCode.seq
    · apply PolyProgram.mapWith_code_eq
      simp only [PolyProgram.comp_code,PolyProgram.pair_code]
      set_code_congr
    · rfl

lemma PolyProgram.minimizeList_code_eq (α β : Type) [TreeCodec α] [TreeCodec β]
    [DecidableEq α] [DecidableEq β] :
    (PolyProgram.minimizeList α).program.code=(PolyProgram.minimizeList β).program.code := by
  simp only [PolyProgram.minimizeList]
  apply congrArg₂ FCode.seq
  · apply congrArg₂ FCode.pair
    · exact PolyProgram.compactCNF_code_eq α β
    · rfl
  · apply PolyProgram.filterWith_code_eq
    exact PolyProgram.minimalClause_code_eq α β

lemma PolyProgram.keepClause_code_eq (α β : Type) [TreeCodec α] [TreeCodec β]
    [DecidableEq α] [DecidableEq β] :
    (PolyProgram.keepClause α).program.code=(PolyProgram.keepClause β).program.code := by
  simp only [PolyProgram.keepClause,PolyProgram.congr_code,PolyProgram.comp_code]
  set_code_congr

lemma PolyProgram.pruneList_code_eq (α β : Type) [TreeCodec α] [TreeCodec β]
    [DecidableEq α] [DecidableEq β] :
    (PolyProgram.pruneList α).program.code=(PolyProgram.pruneList β).program.code := by
  simp only [PolyProgram.pruneList]
  apply congrArg₂ FCode.seq
  · apply congrArg₂ FCode.seq
    · apply congrArg₂ FCode.pair
      · apply PolyProgram.filterWith_code_eq
        exact PolyProgram.keepClause_code_eq α β
      · rfl
    · exact PolyProgram.append_code_eq (List α) (List β)
  · exact PolyProgram.compactCNF_code_eq α β

lemma PolyProgram.prependAll_code_eq (α β : Type) [TreeCodec α] [TreeCodec β] :
    (PolyProgram.prependAll α).program.code=(PolyProgram.prependAll β).program.code := by
  simp only [PolyProgram.prependAll,PolyProgram.comp_code]
  code_congr

lemma PolyProgram.allTuples_code_eq (α β : Type) [TreeCodec α] [TreeCodec β] (n : ℕ) :
    (PolyProgram.allTuples α n).program.code=(PolyProgram.allTuples β n).program.code := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [PolyProgram.allTuples]
    repeat' first
    | apply congrArg₂ FCode.seq
    | apply congrArg₂ FCode.pair
    | apply PolyProgram.mapWith_code_eq
    | apply PolyProgram.prependAll_code_eq
    | apply PolyProgram.flatten_code_eq
    | exact ih
    | rfl

lemma PolyProgram.clauseDiff_code_eq (α β : Type) [TreeCodec α] [TreeCodec β]
    [DecidableEq α] [DecidableEq β] :
    (PolyProgram.clauseDiff α).program.code=(PolyProgram.clauseDiff β).program.code := by
  simp only [PolyProgram.clauseDiff,PolyProgram.congr_code]
  apply PolyProgram.filterWith_code_eq
  simp only [PolyProgram.comp_code]
  set_code_congr

lemma PolyProgram.clauseDisjoint_code_eq (α β : Type) [TreeCodec α] [TreeCodec β]
    [DecidableEq α] [DecidableEq β] :
    (PolyProgram.clauseDisjoint α).program.code=(PolyProgram.clauseDisjoint β).program.code := by
  simp only [PolyProgram.clauseDisjoint,PolyProgram.congr_code,PolyProgram.comp_code]
  set_code_congr

lemma PolyProgram.allWith_code_eq {α β γ δ : Type} [TreeCodec α] [TreeCodec β]
    [TreeCodec γ] [TreeCodec δ] {f : α × γ → Bool} {g : β × δ → Bool}
    (P : PolyProgram (α × γ) Bool f) (Q : PolyProgram (β × δ) Bool g)
    (h : P.program.code=Q.program.code) : P.allWith.program.code=Q.allWith.program.code := by
  simp only [PolyProgram.allWith,PolyProgram.congr_code,PolyProgram.comp_code]
  code_congr

lemma PolyProgram.card_code_eq (α β : Type) [TreeCodec α] [TreeCodec β]
    [DecidableEq α] [DecidableEq β] :
    (PolyProgram.card α).program.code=(PolyProgram.card β).program.code := by
  simp only [PolyProgram.card,PolyProgram.congr_code,PolyProgram.comp_code]
  apply congrArg₂ FCode.seq
  · apply PolyProgram.dedupBy_code_eq
    rfl
  · exact PolyProgram.length_code_eq α β

lemma PolyProgram.cnfCard_code_eq (α β : Type) [TreeCodec α] [TreeCodec β]
    [DecidableEq α] [DecidableEq β] :
    (PolyProgram.cnfCard α).program.code=(PolyProgram.cnfCard β).program.code := by
  simp only [PolyProgram.cnfCard,PolyProgram.congr_code,PolyProgram.comp_code]
  set_code_congr

lemma PolyProgram.cardEq_code_eq (α β : Type) [TreeCodec α] [TreeCodec β]
    [DecidableEq α] [DecidableEq β] (n : ℕ) :
    (PolyProgram.cardEq α n).program.code=(PolyProgram.cardEq β n).program.code := by
  simp only [PolyProgram.cardEq,PolyProgram.comp_code,PolyProgram.pair_code]
  repeat' first
  | apply congrArg₂ FCode.seq
  | apply congrArg₂ FCode.pair
  | apply PolyProgram.card_code_eq
  | rfl

macro "flower_code_congr" : tactic => `(tactic|
  repeat' first
  | with_reducible apply congrArg₂ FCode.seq | with_reducible apply congrArg₂ FCode.pair | with_reducible apply FCode.cond_congr
  | with_reducible apply PolyProgram.mapWith_code_eq | with_reducible apply PolyProgram.map_code_eq
  | with_reducible apply PolyProgram.filterWith_code_eq | with_reducible apply PolyProgram.filter_code_eq
  | with_reducible apply PolyProgram.any_code_eq | with_reducible apply PolyProgram.all_code_eq | with_reducible apply PolyProgram.allWith_code_eq
  | with_reducible apply PolyProgram.compactCNF_code_eq | with_reducible apply PolyProgram.clauseSubset_code_eq
  | with_reducible apply PolyProgram.clauseEqual_code_eq | with_reducible apply PolyProgram.mem_code_eq
  | with_reducible apply PolyProgram.append_code_eq | with_reducible apply PolyProgram.flatten_code_eq | with_reducible apply PolyProgram.length_code_eq
  | with_reducible apply PolyProgram.clauseDisjoint_code_eq | with_reducible apply PolyProgram.clauseDiff_code_eq
  | with_reducible apply PolyProgram.cardEq_code_eq | with_reducible apply PolyProgram.cnfCard_code_eq
  | with_reducible apply PolyProgram.allTuples_code_eq | rfl)

lemma PolyProgram.petalsApart_code_eq (α β : Type) [TreeCodec α] [TreeCodec β]
    [DecidableEq α] [DecidableEq β] :
    (PolyProgram.petalsApart α).program.code=(PolyProgram.petalsApart β).program.code := by
  unfold PolyProgram.petalsApart
  simp only [PolyProgram.congr_code,PolyProgram.comp_code,PolyProgram.pair_code]
  with_reducible apply congrArg₂ FCode.seq
  · rfl
  · with_reducible apply PolyProgram.allWith_code_eq
    simp only [PolyProgram.comp_code]
    with_reducible apply congrArg₂ FCode.seq
    · rfl
    · with_reducible apply PolyProgram.allWith_code_eq
      simp only [PolyProgram.comp_code,PolyProgram.pair_code]
      flower_code_congr

lemma PolyProgram.clauseMember_code_eq (α β : Type) [TreeCodec α] [TreeCodec β]
    [DecidableEq α] [DecidableEq β] :
    (PolyProgram.clauseMember α).program.code=(PolyProgram.clauseMember β).program.code := by
  unfold PolyProgram.clauseMember
  simp only [PolyProgram.congr_code,PolyProgram.comp_code]
  flower_code_congr

lemma PolyProgram.flowerCover_code_eq (α β : Type) [TreeCodec α] [TreeCodec β]
    [DecidableEq α] [DecidableEq β] :
    (PolyProgram.flowerCover α).program.code=(PolyProgram.flowerCover β).program.code := by
  unfold PolyProgram.flowerCover
  simp only [PolyProgram.congr_code,PolyProgram.comp_code]
  with_reducible apply congrArg₂ FCode.seq
  · rfl
  · with_reducible apply PolyProgram.allWith_code_eq
    simp only [PolyProgram.comp_code,PolyProgram.pair_code]
    with_reducible apply congrArg₂ FCode.seq
    · flower_code_congr
    · exact PolyProgram.clauseMember_code_eq α β

lemma PolyProgram.goodFlower_code_eq (α β : Type) [TreeCodec α] [TreeCodec β]
    [DecidableEq α] [DecidableEq β] (p q h : ℕ) :
    (PolyProgram.goodFlower α p q h).program.code=(PolyProgram.goodFlower β p q h).program.code := by
  unfold PolyProgram.goodFlower
  simp only [PolyProgram.congr_code,PolyProgram.comp_code,PolyProgram.pair_code]
  repeat' first
  | with_reducible apply congrArg₂ FCode.seq | with_reducible apply congrArg₂ FCode.pair
  | with_reducible apply PolyProgram.flowerCover_code_eq | with_reducible apply PolyProgram.petalsApart_code_eq
  | with_reducible apply PolyProgram.cardEq_code_eq | with_reducible apply PolyProgram.cnfCard_code_eq
  | (with_reducible apply PolyProgram.all_code_eq; flower_code_congr)
  | (with_reducible apply PolyProgram.allWith_code_eq; simp only [PolyProgram.comp_code]; flower_code_congr)
  | with_reducible rfl
  all_goals first
  | exact PolyProgram.all_code_eq _ _ (PolyProgram.cardEq_code_eq α β q)
  | rfl

lemma PolyProgram.flowerCandidates_code_eq (α β : Type) [TreeCodec α] [TreeCodec β]
    [DecidableEq α] [DecidableEq β] (p h : ℕ) :
    (PolyProgram.flowerCandidates α p h).program.code=(PolyProgram.flowerCandidates β p h).program.code := by
  unfold PolyProgram.flowerCandidates
  erw [PolyProgram.congr_code, PolyProgram.congr_code]
  simp only [PolyProgram.comp_code,PolyProgram.pair_code]
  with_reducible apply congrArg₂ FCode.seq
  · with_reducible apply congrArg₂ FCode.seq
    · flower_code_congr
    · with_reducible apply PolyProgram.mapWith_code_eq
      simp only [PolyProgram.comp_code]
      with_reducible apply congrArg₂ FCode.seq
      · rfl
      · with_reducible apply PolyProgram.mapWith_code_eq
        simp only [PolyProgram.comp_code,PolyProgram.pair_code]
        flower_code_congr
  · exact PolyProgram.flatten_code_eq (FlowerRecord α) (FlowerRecord β)

lemma PolyProgram.flowerList_code_eq (α β : Type) [TreeCodec α] [TreeCodec β]
    [DecidableEq α] [DecidableEq β] (p q h : ℕ) :
    (PolyProgram.flowerList α p q h).program.code=(PolyProgram.flowerList β p q h).program.code := by
  unfold PolyProgram.flowerList
  erw [PolyProgram.congr_code, PolyProgram.congr_code]
  simp only [PolyProgram.comp_code,PolyProgram.pair_code]
  with_reducible apply congrArg₂ FCode.seq
  · with_reducible apply congrArg₂ FCode.pair
    · exact PolyProgram.flowerCandidates_code_eq α β p h
    · rfl
  · with_reducible apply PolyProgram.filterWith_code_eq
    exact PolyProgram.goodFlower_code_eq α β p q h

lemma PolyProgram.sparseBranch_code (α : Type) [TreeCodec α] [DecidableEq α] :
    (PolyProgram.sparseBranch α).program.code =
      .pair (.const (boolTree false))
        (.pair (.seq (TExpr.pair TExpr.input.left (.pair TExpr.input.right.left .nil)).compile (PolyProgram.pruneList α).program.code)
          (.seq (TExpr.pair TExpr.input.left TExpr.input.right.right).compile (PolyProgram.pruneList α).program.code)) := by
  unfold PolyProgram.sparseBranch
  exact PolyProgram.congr_code _ _
lemma PolyProgram.sparseBranch_code_eq (α β : Type) [TreeCodec α] [TreeCodec β]
    [DecidableEq α] [DecidableEq β] :
    (PolyProgram.sparseBranch α).program.code=(PolyProgram.sparseBranch β).program.code := by
  rw [PolyProgram.sparseBranch_code,PolyProgram.sparseBranch_code,PolyProgram.pruneList_code_eq α β]

lemma PolyProgram.sparseStep_code_eq (α β : Type) [TreeCodec α] [TreeCodec β]
    [DecidableEq α] [DecidableEq β] (r : ℕ) :
    (PolyProgram.sparseStep α r).program.code=(PolyProgram.sparseStep β r).program.code := by
  unfold PolyProgram.sparseStep
  erw [PolyProgram.congr_code, PolyProgram.congr_code]
  simp only [PolyProgram.comp_code,PolyProgram.pair_code,PolyProgram.ite_code]
  repeat' first
  | with_reducible apply FCode.cond_congr | with_reducible apply congrArg₂ FCode.seq | with_reducible apply congrArg₂ FCode.pair
  | with_reducible apply PolyProgram.flowerList_code_eq | with_reducible apply PolyProgram.sparseBranch_code_eq | with_reducible rfl
  all_goals rfl

end ParityWL.Complexity

end OAI
