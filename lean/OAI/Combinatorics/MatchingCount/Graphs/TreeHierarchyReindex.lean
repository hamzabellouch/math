import Mathlib
import OAI.Combinatorics.MatchingCount.Graphs.LabelOrder
import OAI.Combinatorics.MatchingCount.Tapes.TreeNumberedCodec

namespace OAI

namespace MatchingFPRAS.TreeTyped.Numbered
variable {A B : Type} [Fintype A] [Fintype B] [LinearOrder A] [LinearOrder B]
def orderedIso (A : Type) [Fintype A] [LinearOrder A] : Fin (Fintype.card A)≃o A where
  toEquiv:=UnitRefresh.orderedEnum A
  map_rel_iff' := by intro a b; rw [←not_lt,←not_lt,UnitRefresh.orderedEnum_lt]
lemma index_orderIso (e : A≃o B) (a : A) : index (e a)=index a := by
  let h := Fintype.card_congr e.toEquiv
  have he : (orderedIso A).trans e=(Fin.castOrderIso h).trans (orderedIso B) := Subsingleton.elim _ _
  have hh:=congrArg (fun f : Fin (Fintype.card A)≃o B=>
    ((UnitRefresh.orderedEnum B).symm (f ((UnitRefresh.orderedEnum A).symm a))).val) he
  change ((UnitRefresh.orderedEnum B).symm
    (e (UnitRefresh.orderedEnum A ((UnitRefresh.orderedEnum A).symm a)))).val=
      ((UnitRefresh.orderedEnum B).symm
        (UnitRefresh.orderedEnum B (Fin.cast h ((UnitRefresh.orderedEnum A).symm a)))).val at hh
  simpa only [Equiv.apply_symm_apply,Equiv.symm_apply_apply,Fin.val_cast,index] using hh
end MatchingFPRAS.TreeTyped.Numbered

namespace MatchingFPRAS.NumberedHierarchy
open Finset

variable {V W : Type} [Fintype V] [Fintype W] [LinearOrder V] [LinearOrder W]
variable (B : W→W→ℚ) (e : V≃o W)
abbrev reindex : V→V→ℚ := fun i j=>B (e i) (e j)
lemma component_reindex (t : ℚ) (x y : V) :
    y∈component (reindex B e) t x ↔ e y∈component B t (e x) := by
  simp only [component,mem_filter,mem_univ,true_and,related,reindex,e.injective.eq_iff]
lemma root_reindex (t : ℚ) (x : V) : e (root (reindex B e) t x)=root B t (e x) := by
  apply le_antisymm
  · have hm : e.symm (root B t (e x)) ∈ component (reindex B e) t x := by
      rw [component_reindex,OrderIso.apply_symm_apply]
      exact root_mem B t (e x)
    have hle := Finset.min'_le (component (reindex B e) t x) _ hm
    have hh:=e.monotone hle
    simpa only [OrderIso.apply_symm_apply,root] using hh
  · exact Finset.min'_le (component B t (e x)) _
      ((component_reindex B e t x _).mp (root_mem (reindex B e) t x))

def componentReindex (t : ℚ) : NumberedComponent (reindex B e) t≃NumberedComponent B t where
  toFun x:=⟨e x.val,by rw [←root_reindex B e t x.val,x.property]⟩
  invFun x:=⟨e.symm x.val,by
    apply e.injective
    rw [root_reindex,OrderIso.apply_symm_apply,x.property]⟩
  left_inv x:=Subtype.ext (e.symm_apply_apply x.val)
  right_inv x:=Subtype.ext (e.apply_symm_apply x.val)
def labelReindex (H : ℕ) : Label (reindex B e) H≃Label B H :=
  Equiv.sigmaCongrRight (fun k=>componentReindex B e ((2:ℚ)^k.val))

attribute [local instance] labelOrder
local instance (priority := 2000) {U : Type} [Fintype U] [LinearOrder U] {H : ℕ}
    (C : U→U→ℚ) : LE (Label C H) := (labelOrder C H).toLE

def labelOrderReindex (H : ℕ) : Label (reindex B e) H≃o Label B H where
  toEquiv:=labelReindex B e H
  map_rel_iff' := by
    intro a b
    change toLex (a.1,e a.2.val)≤toLex (b.1,e b.2.val) ↔
      toLex (a.1,a.2.val)≤toLex (b.1,b.2.val)
    simp only [Prod.Lex.le_iff,ofLex_toLex,e.le_iff_le]

lemma labelReindex_index (H : ℕ) (l : Label (reindex B e) H) :
    TreeTyped.Numbered.index (labelReindex B e H l)=TreeTyped.Numbered.index l :=
  TreeTyped.Numbered.index_orderIso (labelOrderReindex B e H) l

open Finset

variable {V W : Type} [Fintype V] [Fintype W] [LinearOrder V] [LinearOrder W]
variable (B : W→W→ℚ) (e : V≃o W)
variable (hsym : ∀ a b,B a b=B b a)
variable (htri : ∀ x y z,x≠y → x≠z → y≠z → min (B x z) (B z y)≤B x y)
omit [Fintype V] [Fintype W] in
include hsym in
lemma reindex_symm : ∀ a b,reindex B e a b=reindex B e b a := fun a b=>hsym (e a) (e b)
omit [Fintype V] [Fintype W] in
include htri in
lemma reindex_tri : ∀ x y z,x≠y → x≠z → y≠z →
    min (reindex B e x z) (reindex B e z y)≤reindex B e x y :=
  fun x y z hxy hxz hyz=>htri (e x) (e y) (e z) (e.injective.ne hxy) (e.injective.ne hxz) (e.injective.ne hyz)
lemma labelAt_reindex {H : ℕ} (k : Fin (H+1)) (x : V) :
    labelReindex B e H (labelAt (reindex B e) (reindex_symm B e hsym)
      (reindex_tri B e htri) k x)=labelAt B hsym htri k (e x) := by
  apply congrArg (Sigma.mk k)
  apply Subtype.ext
  exact root_reindex B e _ x
lemma edgeLabel_reindex {E : Type} [Fintype E] [DecidableEq E]
    (left right : E→W) (H : ℕ) (a : E) :
    labelReindex B e H (edgeLabel (reindex B e) (reindex_symm B e hsym)
      (reindex_tri B e htri) (e.symm ∘ left) (e.symm ∘ right) H a)=
      edgeLabel B hsym htri left right H a := by
  unfold edgeLabel
  simp only [reindex,Function.comp_apply,OrderIso.apply_symm_apply]
  rw [labelAt_reindex,OrderIso.apply_symm_apply]
end MatchingFPRAS.NumberedHierarchy

end OAI
