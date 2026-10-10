import Mathlib
import OAI.Combinatorics.MatchingCount.Machines.TreeEnumeration
import OAI.Combinatorics.MatchingCount.Machines.TreeRefreshIndexed

namespace OAI

namespace MatchingFPRAS.ExecutableRefresh
open TreeTyped ExecutableDP ExecutableSource Polynomial

def sharedKey (x : Bags×Key) : Bool :=
  decide (x.2.2∈x.1.getD x.2.1.1 [] ∧ x.2.2∈x.1.getD x.2.1.2 [])
def sharedKeyRealizer : Realizer sharedKey := (composition (pair
  (composition (pair (composition (pair first second.fst.fst) (getDFast [])) second.snd) membership)
  (composition (pair (composition (pair first second.fst.snd) (getDFast [])) second.snd) membership))
  boolAnd).congr (by intro x; simp [sharedKey])
lemma polynomial_sharedKey : PolynomialTime sharedKeyRealizer := by
  unfold sharedKeyRealizer
  apply polynomial_congr
  dsimp only [Realizer.fst, Realizer.snd]
  have := polynomial_getDFast ([] : List ℕ)
  have := polynomial_membership
  tree_cost

def storedCatalog (x : Bags×List ℕ) : List Key :=
  ((logicalEdges (List.range x.1.length)).product x.2).filter (fun e=>sharedKey (x.1,e))
def storedCatalogRealizer : Realizer storedCatalog := (composition (pair first
  (composition (pair (composition (composition (composition first listLength) range)
    logicalEdgesRealizer) second) listProduct)) (filterWith sharedKeyRealizer)).congr (fun _=>rfl)
lemma polynomial_storedCatalog : PolynomialTime storedCatalogRealizer := by
  have hr : PolynomialTime (composition (composition (first (A:=Bags) (B:=List ℕ)) listLength) range) := by
    apply polynomial_boundedRange (polynomial_composition polynomial_first polynomial_listLength) X
    intro x
    simpa only [eval_X,Function.comp_apply] using (list_length_le_weight x.1).trans (weight_fst x)
  unfold storedCatalogRealizer
  apply polynomial_congr
  have := polynomial_filterWithList polynomial_sharedKey
  have := polynomial_sharedKey
  have := polynomial_logicalEdges
  have := polynomial_listProduct (A:=ℕ×ℕ) (B:=ℕ)
  tree_cost

open Transport UnitRefresh

attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype Transport.prodOrder
local instance (priority := 2000) {A B : Type} [LinearOrder A] [LinearOrder B] : LE (A×B) := Transport.prodOrder.toLE
local instance (priority := 2000) {A B : Type} [LinearOrder A] [LinearOrder B] : LT (A×B) := Transport.prodOrder.toLT
local instance (priority := 2000) {A B : Type} [LinearOrder A] [LinearOrder B] : Preorder (A×B) := Transport.prodOrder.toPreorder
local instance (priority := 2000) {V : Type} [LinearOrder V] : LT (Sym2 V) := Transport.sym2Order.toLT
local instance (priority := 2000) {V : Type} [LinearOrder V] : LE (Sym2 V) := Transport.sym2Order.toLE
variable {n m : ℕ} {bags : Fin n→Finset (Fin m)} {a : Bags}
lemma key_le (e f : BagEdge bags) : @LE.le Key Transport.prodOrder.toLE (key e) (key f) ↔ @LE.le _ Transport.bagEdgeOrder.toLE e f := by
  change toLex (key e) ≤ toLex (key f) ↔ toLex e.val.val ≤ toLex f.val.val
  simp only [Prod.Lex.le_iff,key,ofLex_toLex,Fin.le_def]
  have hlt : (e.val.val.1.inf.val,e.val.val.1.sup.val)<(f.val.val.1.inf.val,f.val.val.1.sup.val) ↔ e.val.val.1<f.val.val.1 := by
    change toLex (e.val.val.1.inf.val,e.val.val.1.sup.val)<toLex (f.val.val.1.inf.val,f.val.val.1.sup.val) ↔
      toLex (Sym2.sortEquiv e.val.val.1).val<toLex (Sym2.sortEquiv f.val.val.1).val
    simp only [Prod.Lex.lt_iff,ofLex_toLex,Fin.lt_def,Fin.val_inj,Sym2.sortEquiv]
    rfl
  have heq : (e.val.val.1.inf.val,e.val.val.1.sup.val)=(f.val.val.1.inf.val,f.val.val.1.sup.val) ↔ e.val.val.1=f.val.val.1 := by
    constructor
    · intro h
      apply Sym2.sortEquiv.injective
      apply Subtype.ext
      apply Prod.ext <;> apply Fin.ext
      · exact congrArg Prod.fst h
      · exact congrArg Prod.snd h
    · intro h; rw [h]
  rw [hlt,heq]
lemma row_mem (ha : List.Forall₂ List.Perm a (orderedRep bags)) (i : Fin n) (j : ℕ) :
    j∈a.getD i.val [] ↔ ∃ c∈bags i,c.val=j := by
  rw [(rows_getD ha i.val).mem_iff]
  simp only [orderedRep,List.getD,List.getElem?_ofFn,i.isLt,↓reduceDIte,Option.getD_some,bagRep,List.mem_map,Finset.mem_toList]
lemma sym_mk_inf_sup (s : Sym2 (Fin n)) : s(s.inf,s.sup)=s :=
  (Sym2.sortEquiv.symm_apply_apply s)
lemma sym_inf_mem (s : Sym2 (Fin n)) : s.inf∈s := by
  have h:=Sym2.mem_mk_left s.inf s.sup
  rwa [sym_mk_inf_sup] at h
lemma sym_sup_mem (s : Sym2 (Fin n)) : s.sup∈s := by
  have h:=Sym2.mem_mk_right s.inf s.sup
  rwa [sym_mk_inf_sup] at h
lemma storedCatalog_mem (ha : List.Forall₂ List.Perm a (orderedRep bags)) (e : Key) :
    e∈storedCatalog (a,List.range m) ↔ ∃ b : BagEdge bags,key b=e := by
  have hn : a.length=n := by simpa only [orderedRep,List.length_ofFn] using ha.length_eq
  constructor
  · intro he
    obtain ⟨he,hs⟩:=List.mem_filter.mp he
    obtain ⟨he,hc⟩:=List.mem_product.mp he
    obtain ⟨he,huv⟩:=List.mem_filter.mp he
    obtain ⟨hu,hv⟩:=List.mem_product.mp he
    have hu : e.1.1<n := by simpa only [List.mem_range,hn] using hu
    have hv : e.1.2<n := by simpa only [List.mem_range,hn] using hv
    have hc : e.2 < m := List.mem_range.mp hc
    have huv : e.1.1<e.1.2 := of_decide_eq_true huv
    have hs : e.2∈a.getD e.1.1 [] ∧ e.2∈a.getD e.1.2 [] := of_decide_eq_true hs
    have hcu': (⟨e.2,hc⟩ : Fin m)∈bags ⟨e.1.1,hu⟩ := by
      obtain ⟨l,hl,he⟩:=(row_mem ha ⟨e.1.1,hu⟩ e.2).mp hs.1
      have he' : l=(⟨e.2,hc⟩ : Fin m) := Fin.ext he
      simpa only [he'] using hl
    have hcv': (⟨e.2,hc⟩ : Fin m)∈bags ⟨e.1.2,hv⟩ := by
      obtain ⟨l,hl,he⟩:=(row_mem ha ⟨e.1.2,hv⟩ e.2).mp hs.2
      have he' : l=(⟨e.2,hc⟩ : Fin m) := Fin.ext he
      simpa only [he'] using hl
    have huv' : (⟨e.1.1,hu⟩ : Fin n)<⟨e.1.2,hv⟩ := huv
    let b : BagEdge bags:=⟨⟨(s((⟨e.1.1,hu⟩ : Fin n),⟨e.1.2,hv⟩),(⟨e.2,hc⟩ : Fin m)),by
      simp only [Sym2.mk_isDiag_iff]; exact ne_of_lt huv'⟩,by
      intro i hi
      rcases Sym2.mem_iff.mp hi with rfl|rfl
      · exact hcu'
      · exact hcv'⟩
    refine ⟨b,?_⟩
    simp only [key,b,Sym2.inf_mk,Sym2.sup_mk,inf_eq_left.mpr huv'.le,sup_eq_right.mpr huv'.le]
  · rintro ⟨b,rfl⟩
    have hlt : b.val.val.1.inf<b.val.val.1.sup := lt_of_le_of_ne b.val.val.1.inf_le_sup (by
      intro h
      apply b.val.property
      rw [←sym_mk_inf_sup b.val.val.1,h]
      exact Sym2.mk_isDiag_iff.mpr rfl)
    apply List.mem_filter.mpr
    constructor
    · apply List.mem_product.mpr
      constructor
      · apply List.mem_filter.mpr
        constructor
        · exact List.mem_product.mpr ⟨List.mem_range.mpr (by simpa only [hn] using b.val.val.1.inf.isLt),
            List.mem_range.mpr (by simpa only [hn] using b.val.val.1.sup.isLt)⟩
        · exact decide_eq_true hlt
      · exact List.mem_range.mpr b.val.val.2.isLt
    · apply decide_eq_true
      constructor
      · exact (row_mem ha _ _).mpr ⟨b.val.val.2,b.property _ (sym_inf_mem _),rfl⟩
      · exact (row_mem ha _ _).mpr ⟨b.val.val.2,b.property _ (sym_sup_mem _),rfl⟩
lemma storedCatalog_eq (ha : List.Forall₂ List.Perm a (orderedRep bags)) :
    storedCatalog (a,List.range m)=catalog bags := by
  have hpair : (storedCatalog (a,List.range m)).Pairwise (· < ·) := by
    apply List.Pairwise.filter
    exact pairwise_product (logicalEdges_pairwise a.length) List.pairwise_lt_range
  have hn := hpair.imp (fun h=>h.ne)
  have hc : (catalog bags).Nodup := List.nodup_ofFn.mpr
    ((key_injective (bags:=bags)).comp (orderedEnum (BagEdge bags)).injective)
  have hp : (storedCatalog (a,List.range m)).Perm (catalog bags) := by
    apply (List.perm_ext_iff_of_nodup hn hc).mpr
    intro e
    rw [storedCatalog_mem ha]
    simp only [catalog,List.mem_ofFn]
    constructor
    · rintro ⟨b,rfl⟩; exact ⟨(orderedEnum _).symm b,by simp⟩
    · rintro ⟨i,rfl⟩; exact ⟨(orderedEnum _ i),rfl⟩
  apply hp.eq_of_pairwise (fun _ _ _ _ h₁ h₂=>@le_antisymm _ Transport.prodOrder.toPartialOrder _ _ h₁ h₂)
    (hpair.imp (fun h=>le_of_lt h))
  rw [catalog,show (fun i=>key (orderedEnum (BagEdge bags) i))=key ∘ orderedEnum (BagEdge bags) from rfl,
    ←List.map_ofFn,ofFn_orderedEnum]
  apply List.pairwise_map.mpr
  exact (Finset.pairwise_sort _ _).imp (fun h=>(key_le _ _).mpr h)
end MatchingFPRAS.ExecutableRefresh

end OAI
