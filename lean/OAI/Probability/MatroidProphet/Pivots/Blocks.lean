import OAI.Probability.MatroidProphet.Pivots.Reindex
import Mathlib.Data.Prod.Lex
import Mathlib.Order.WithBot

namespace OAI

namespace MatroidProphet.Pivots

open Set Finset

variable {α A T : Type*} [Fintype α] [LinearOrder α] [Fintype A] [Fintype T] [LinearOrder T]

abbrev BlockOld (F : T → Set α) :=
  {p : T ×ₗ α // (ofLex p).2 ∈ F (ofLex p).1}

noncomputable instance (F : T → Set α) : Fintype (BlockOld F) := Fintype.ofFinite _

def blockOldStage {F : T → Set α} (o : BlockOld F) : T := (ofLex o.val).1

def blockOldLabel {F : T → Set α} (o : BlockOld F) : α := (ofLex o.val).2

def blockStage (F : T → Set α) (τ : A → T) : BlockOld F ⊕ A → T :=
  Sum.elim (blockOldStage (F := F)) τ

noncomputable def blockKey (F : T → Set α) (τ : A → T) :
    BlockOld F ⊕ A → T ×ₗ (WithTop α ×ₗ ℕ)
  | Sum.inl o => toLex (blockOldStage (F := F) o, toLex ((blockOldLabel (α := α) (F := F) o : WithTop α), 0))
  | Sum.inr a => toLex (τ a, toLex (⊤, ((Fintype.equivFin A) a).val))

lemma blockKey_injective
    {α : Type u_1} {A : Type u_2} {T : Type u_3}
    [Fintype α] [LinearOrder α] [Fintype A] [Fintype T] [LinearOrder T]
    (F : T → Set α) (τ : A → T) :
    Function.Injective (blockKey F τ) := by
  intro x y h
  cases x with
  | inl x =>
    cases y with
    | inl y =>
      have hs : blockOldStage (F := F) x = blockOldStage (F := F) y := congrArg (fun z => (ofLex z).1) h
      have hl : (blockOldLabel (α := α) (F := F) x : WithTop α) = blockOldLabel (α := α) (F := F) y :=
        congrArg (fun z => (ofLex (ofLex z).2).1) h
      have hl' : blockOldLabel (α := α) (F := F) x = blockOldLabel (α := α) (F := F) y := WithTop.coe_inj.mp hl
      have heq : x = y := Subtype.ext (congrArg toLex (Prod.ext hs hl'))
      exact congrArg Sum.inl heq
    | inr y =>
      have hh : (blockOldLabel (α := α) (F := F) x : WithTop α) = ⊤ :=
        congrArg (fun z => (ofLex (ofLex z).2).1) h
      exact (WithTop.coe_ne_top hh).elim
  | inr x =>
    cases y with
    | inl y =>
      have hh : (blockOldLabel (α := α) (F := F) y : WithTop α) = ⊤ :=
        (congrArg (fun z => (ofLex (ofLex z).2).1) h).symm
      exact (WithTop.coe_ne_top hh).elim
    | inr y =>
      have hi : ((Fintype.equivFin A) x).val = ((Fintype.equivFin A) y).val :=
        congrArg (fun z => (ofLex (ofLex z).2).2) h
      exact congrArg Sum.inr ((Fintype.equivFin A).injective (Fin.ext hi))

noncomputable def blockTime (F : T → Set α) (τ : A → T) : BlockOld F ⊕ A → ℕ := by
  letI := LinearOrder.lift' (blockKey F τ) (blockKey_injective F τ)
  exact fun o => ((Fintype.orderIsoFinOfCardEq (BlockOld F ⊕ A) rfl).symm o).val

lemma blockTime_lt_iff (F : T → Set α) (τ : A → T) (x y : BlockOld F ⊕ A) :
    blockTime F τ x < blockTime F τ y ↔ blockKey F τ x < blockKey F τ y := by
  let := LinearOrder.lift' (blockKey F τ) (blockKey_injective F τ)
  change (Fintype.orderIsoFinOfCardEq (BlockOld F ⊕ A) rfl).symm x <
    (Fintype.orderIsoFinOfCardEq (BlockOld F ⊕ A) rfl).symm y ↔ _
  exact OrderIso.lt_iff_lt _

lemma blockTime_injective (F : T → Set α) (τ : A → T) :
    Function.Injective (blockTime F τ) := by
  intro x y h
  apply blockKey_injective F τ
  apply le_antisymm <;> apply le_of_not_gt <;> intro hh
  · exact (lt_irrefl _ (h ▸ (blockTime_lt_iff F τ y x).2 hh))
  · exact (lt_irrefl _ (h ▸ (blockTime_lt_iff F τ x y).2 hh))

lemma blockTime_old_strictMono (F : T → Set α) (τ : A → T) :
    StrictMono (fun o : BlockOld F => blockTime F τ (Sum.inl o)) := by
  intro x y hxy
  apply (blockTime_lt_iff F τ _ _).2
  change toLex (blockOldStage (F := F) x, toLex ((blockOldLabel (α := α) (F := F) x : WithTop α), 0)) <
    toLex (blockOldStage (F := F) y, toLex ((blockOldLabel (α := α) (F := F) y : WithTop α), 0))
  have hh : x.val < y.val := hxy
  rcases Prod.Lex.toLex_lt_toLex.mp hh with hs | ⟨hs, hl⟩
  · exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl hs)
  · exact Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨hs,
      Prod.Lex.toLex_lt_toLex.mpr (Or.inl (WithTop.coe_lt_coe.mpr hl))⟩)

lemma stage_lt_implies_blockTime_lt (F : T → Set α) (τ : A → T)
    {x y : BlockOld F ⊕ A} (h : blockStage F τ x < blockStage F τ y) :
    blockTime F τ x < blockTime F τ y := by
  apply (blockTime_lt_iff F τ _ _).2
  apply Prod.Lex.toLex_lt_toLex.mpr
  left
  cases x <;> cases y <;> exact h

lemma blockTime_le_implies_stage_le (F : T → Set α) (τ : A → T)
    {x y : BlockOld F ⊕ A} (h : blockTime F τ x ≤ blockTime F τ y) :
    blockStage F τ x ≤ blockStage F τ y := by
  by_contra hh
  exact (not_lt_of_ge h) (stage_lt_implies_blockTime_lt F τ (lt_of_not_ge hh))

end MatroidProphet.Pivots

end OAI
