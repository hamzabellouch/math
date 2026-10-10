import OAI.Combinatorics.ParityLifts.CodeErasure

namespace OAI

namespace ParityWL.Complexity

lemma FEval.output_unique {S T : ℕ} {p : FCode} {x y z : DataTree} {n m : ℕ}
    (h : FEval S p x n y) (h' : FEval T p x m z) : y=z := by
  induction h using FEval.rec generalizing T m z with
  | id x hx => cases h'; rfl
  | nil x hx => cases h'; rfl
  | left x hx => cases h'; rfl
  | right x hx => cases h'; rfl
  | pair hf hg hb ihf ihg =>
    cases h' with
    | pair hf' hg' hb' => exact congrArg₂ DataTree.node (ihf hf') (ihg hg')
  | seq hf hg ihf ihg =>
    cases h' with
    | seq hf' hg' =>
      have he := ihf hf'
      subst he
      exact ihg hg'
  | nil_branch hf ih =>
    cases h' with
    | nil_branch hf' => exact ih hf'
    | node_branch hx hg => exact False.elim (hx rfl)
  | node_branch hx hg ih =>
    cases h' with
    | nil_branch hf' => exact False.elim (hx rfl)
    | node_branch hx' hg' => exact ih hg'
  | nil_cond hp hf ihp ihf =>
    cases h' with
    | nil_cond hp' hf' => exact ihf hf'
    | node_cond hp' hz hg => exact False.elim (hz (ihp hp').symm)
  | node_cond hp hz hg ihp ihg =>
    cases h' with
    | nil_cond hp' hf' => exact False.elim (hz (ihp hp'))
    | node_cond hp' hz' hg' => exact ihg hg'
  | loop_stop f x hx he =>
    cases h' with
    | loop_stop => rfl
    | loop_next he' h tail => exact False.elim (he' he)
  | loop_next he h tail ih iht =>
    cases h' with
    | loop_stop f x hx he' => exact False.elim (he he')
    | loop_next he' h' tail' =>
      have hy := ih h'
      subst hy
      exact iht tail'

lemma BEval.output_unique {p : FCode} {x y z : DataTree} {B C : ℕ}
    (h : BEval p x B y) (h' : BEval p x C z) : y=z :=
  h.choose_spec.2.output_unique h'.choose_spec.2

lemma PolyProgram.encoding_natural {α β γ δ : Type} [TreeCodec α] [TreeCodec β]
    [TreeCodec γ] [TreeCodec δ] {f : α → β} {g : γ → δ}
    (P : PolyProgram α β f) (Q : PolyProgram γ δ g)
    (h : P.program.code=Q.program.code) (a : α) (c : γ) (hac : treeEncode a=treeEncode c) :
    treeEncode (f a)=treeEncode (g c) := by
  have hp := P.program.run a
  rw [h,hac] at hp
  exact hp.output_unique (Q.program.run c)

lemma treeEncode_map {α β : Type} [TreeCodec α] [TreeCodec β] (f : α → β)
    (h : ∀ a, treeEncode (f a)=treeEncode a) (xs : List α) :
    treeEncode (xs.map f)=treeEncode xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp only [List.map_cons,treeEncode_cons,h,ih]

end ParityWL.Complexity

end OAI
