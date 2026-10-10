import Mathlib
import OAI.Combinatorics.MatchingCount.Machines.TreeRefreshCatalog

namespace OAI

namespace MatchingFPRAS.ExecutableRefresh
open TreeTyped TreeTyped.Numbered ExecutableDP ExecutableUnit Transport UnitRefresh

attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype Transport.prodOrder
local instance (priority := 2000) {A B : Type} [LinearOrder A] [LinearOrder B] : LE (A×B) := Transport.prodOrder.toLE
local instance (priority := 2000) {A B : Type} [LinearOrder A] [LinearOrder B] : LT (A×B) := Transport.prodOrder.toLT
local instance (priority := 2000) {A B : Type} [LinearOrder A] [LinearOrder B] : Preorder (A×B) := Transport.prodOrder.toPreorder
local instance (priority := 2000) {V : Type} [LinearOrder V] : LT (Sym2 V) := Transport.sym2Order.toLT
local instance (priority := 2000) {V : Type} [LinearOrder V] : LE (Sym2 V) := Transport.sym2Order.toLE
variable {V L : Type} [Fintype V] [LinearOrder V] [Fintype L] [LinearOrder L]
variable {bags : V→Finset L}
def sourceKey (e : BagEdge bags) : Key :=
  ((Numbered.index e.val.val.1.inf,Numbered.index e.val.val.1.sup),Numbered.index e.val.val.2)
def sourceCatalog (bags : V→Finset L) : List Key :=
  List.ofFn (fun i=>sourceKey (orderedEnum (BagEdge bags) i))
lemma sourceKey_injective : Function.Injective (sourceKey (bags:=bags)) := by
  intro a b h
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · apply Sym2.sortEquiv.injective
    apply Subtype.ext
    apply Prod.ext
    · exact Numbered.index_injective (congrArg (fun z=>z.1.1) h)
    · exact Numbered.index_injective (congrArg (fun z=>z.1.2) h)
  · exact Numbered.index_injective (congrArg Prod.snd h)
lemma index_lt (a b : V) : Numbered.index a < Numbered.index b ↔ a<b := by
  rw [lt_iff_not_ge,lt_iff_not_ge,Numbered.index_le]
lemma sourceKey_le (e f : BagEdge bags) :
    @LE.le Key Transport.prodOrder.toLE (sourceKey e) (sourceKey f) ↔
      @LE.le _ Transport.bagEdgeOrder.toLE e f := by
  change toLex (sourceKey e)≤toLex (sourceKey f) ↔ toLex e.val.val≤toLex f.val.val
  simp only [Prod.Lex.le_iff,sourceKey,ofLex_toLex,Numbered.index_le]
  have hlt : (Numbered.index e.val.val.1.inf,Numbered.index e.val.val.1.sup)<
      (Numbered.index f.val.val.1.inf,Numbered.index f.val.val.1.sup) ↔ e.val.val.1<f.val.val.1 := by
    change toLex (Numbered.index e.val.val.1.inf,Numbered.index e.val.val.1.sup)<
      toLex (Numbered.index f.val.val.1.inf,Numbered.index f.val.val.1.sup) ↔
      toLex (Sym2.sortEquiv e.val.val.1).val<toLex (Sym2.sortEquiv f.val.val.1).val
    simp only [Prod.Lex.lt_iff,ofLex_toLex,index_lt,Numbered.index_injective.eq_iff]
    rfl
  have heq : (Numbered.index e.val.val.1.inf,Numbered.index e.val.val.1.sup)=
      (Numbered.index f.val.val.1.inf,Numbered.index f.val.val.1.sup) ↔ e.val.val.1=f.val.val.1 := by
    constructor
    · intro h
      apply Sym2.sortEquiv.injective
      apply Subtype.ext
      exact Prod.ext (Numbered.index_injective (congrArg Prod.fst h))
        (Numbered.index_injective (congrArg Prod.snd h))
    · intro h; rw [h]
  rw [hlt,heq]
lemma sourceCatalog_index (e : BagEdge bags) :
    (sourceCatalog bags).idxOf (sourceKey e)=Numbered.index e := by
  let i := (orderedEnum (BagEdge bags)).symm e
  have hn : (sourceCatalog bags).Nodup := List.nodup_ofFn.mpr
    ((sourceKey_injective (bags:=bags)).comp (orderedEnum (BagEdge bags)).injective)
  have hi : i.val<(sourceCatalog bags).length := by simp only [sourceCatalog,List.length_ofFn]; exact i.isLt
  dsimp only [sourceCatalog] at hi hn
  have h:=@List.Nodup.idxOf_getElem Key (inferInstance : BEq Key) inferInstance _ hn i.val hi
  have hh : (List.ofFn (fun j=>sourceKey (orderedEnum (BagEdge bags) j)))[i.val]'hi=sourceKey e := by
    rw [List.getElem_ofFn]
    simp only [Fin.eta,i,Equiv.apply_symm_apply]
  rw [hh] at h
  exact h
lemma sourceCatalog_pairwise : (sourceCatalog bags).Pairwise (· ≤ ·) := by
  rw [sourceCatalog,show (fun i=>sourceKey (orderedEnum (BagEdge bags) i))=
    sourceKey ∘ orderedEnum (BagEdge bags) from rfl,←List.map_ofFn,ofFn_orderedEnum]
  apply List.pairwise_map.mpr
  exact (Finset.pairwise_sort _ _).imp (fun h=>(sourceKey_le _ _).mpr h)
omit [Fintype V] in
lemma source_inf_mem (s : Sym2 V) : s.inf∈s := by
  have h:=Sym2.mem_mk_left s.inf s.sup
  have hs : s(s.inf,s.sup)=s := Sym2.sortEquiv.symm_apply_apply s
  rwa [hs] at h
omit [Fintype V] in
lemma source_sup_mem (s : Sym2 V) : s.sup∈s := by
  have h:=Sym2.mem_mk_right s.inf s.sup
  have hs : s(s.inf,s.sup)=s := Sym2.sortEquiv.symm_apply_apply s
  rwa [hs] at h
omit [Fintype V] [Fintype L] [LinearOrder L] in
lemma edge_inf_lt_sup (e : BagEdge bags) : e.val.val.1.inf<e.val.val.1.sup := by
  apply lt_of_le_of_ne e.val.val.1.inf_le_sup
  intro h
  apply e.val.property
  rw [←Sym2.sortEquiv.symm_apply_apply e.val.val.1]
  change s(e.val.val.1.inf,e.val.val.1.sup).IsDiag
  rw [h]
  exact Sym2.mk_isDiag_iff.mpr rfl

def downEdge (e : BagEdge bags) : BagEdge (numberedBags bags) :=
  ⟨⟨(s((orderedEnum V).symm e.val.val.1.inf,(orderedEnum V).symm e.val.val.1.sup),
    (orderedEnum L).symm e.val.val.2),by
      rw [Sym2.mk_isDiag_iff]
      exact fun h=>(ne_of_lt (edge_inf_lt_sup e)) ((orderedEnum V).symm.injective h)⟩,by
    intro i hi
    rcases Sym2.mem_iff.mp hi with rfl|rfl
    · rw [mem_numberedBags]
      simpa only [ColoredEdge.color,Equiv.apply_symm_apply] using e.property _ (source_inf_mem _)
    · rw [mem_numberedBags]
      simpa only [ColoredEdge.color,Equiv.apply_symm_apply] using e.property _ (source_sup_mem _)⟩
lemma key_downEdge (e : BagEdge bags) : key (downEdge e)=sourceKey e := by
  have h : (orderedEnum V).symm e.val.val.1.inf≤(orderedEnum V).symm e.val.val.1.sup := by
    change Numbered.index e.val.val.1.inf≤Numbered.index e.val.val.1.sup
    exact (Numbered.index_le _ _).mpr e.val.val.1.inf_le_sup
  simp only [key,downEdge,Sym2.inf_mk,Sym2.sup_mk,inf_eq_left.mpr h,sup_eq_right.mpr h,sourceKey,Numbered.index]

def upEdge (e : BagEdge (numberedBags bags)) : BagEdge bags :=
  ⟨⟨(s(orderedEnum V e.val.val.1.inf,orderedEnum V e.val.val.1.sup),
    orderedEnum L e.val.val.2),by
      rw [Sym2.mk_isDiag_iff]
      exact fun h=>(ne_of_lt (edge_inf_lt_sup e)) ((orderedEnum V).injective h)⟩,by
    intro i hi
    rcases Sym2.mem_iff.mp hi with rfl|rfl
    · exact (mem_numberedBags bags _ _).mp (e.property _ (sym_inf_mem _))
    · exact (mem_numberedBags bags _ _).mp (e.property _ (sym_sup_mem _))⟩
lemma sourceKey_upEdge (e : BagEdge (numberedBags bags)) : sourceKey (upEdge e)=key e := by
  have h : orderedEnum V e.val.val.1.inf≤orderedEnum V e.val.val.1.sup := by
    exact ((Numbered.index_le _ _).mp (by simpa only [Numbered.index_orderedEnum,Fin.le_def] using e.val.val.1.inf_le_sup))
  simp only [sourceKey,upEdge,Sym2.inf_mk,Sym2.sup_mk,inf_eq_left.mpr h,sup_eq_right.mpr h,Numbered.index_orderedEnum,key]

lemma sourceCatalog_eq : sourceCatalog bags=catalog (numberedBags bags) := by
  have ha : (sourceCatalog bags).Nodup := List.nodup_ofFn.mpr
    ((sourceKey_injective (bags:=bags)).comp (orderedEnum (BagEdge bags)).injective)
  have hb : (catalog (numberedBags bags)).Nodup := List.nodup_ofFn.mpr
    ((key_injective (bags:=numberedBags bags)).comp (orderedEnum (BagEdge (numberedBags bags))).injective)
  have hp : (sourceCatalog bags).Perm (catalog (numberedBags bags)) := by
    apply (List.perm_ext_iff_of_nodup ha hb).mpr
    intro k
    simp only [sourceCatalog,catalog,List.mem_ofFn]
    constructor
    · rintro ⟨i,rfl⟩
      refine ⟨(orderedEnum _).symm (downEdge (orderedEnum _ i)),?_⟩
      rw [Equiv.apply_symm_apply,key_downEdge]
    · rintro ⟨i,rfl⟩
      refine ⟨(orderedEnum _).symm (upEdge (orderedEnum _ i)),?_⟩
      rw [Equiv.apply_symm_apply,sourceKey_upEdge]
  apply hp.eq_of_pairwise (fun _ _ _ _ h₁ h₂=>@le_antisymm _ Transport.prodOrder.toPartialOrder _ _ h₁ h₂) sourceCatalog_pairwise
  rw [catalog,show (fun i=>key (orderedEnum (BagEdge (numberedBags bags)) i))=
    key ∘ orderedEnum (BagEdge (numberedBags bags)) from rfl,←List.map_ofFn,ofFn_orderedEnum]
  apply List.pairwise_map.mpr
  exact (Finset.pairwise_sort _ _).imp (fun h=>(key_le _ _).mpr h)
end MatchingFPRAS.ExecutableRefresh

end OAI
